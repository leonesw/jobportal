#!/usr/bin/env python3
"""
Stellenradar – Sammel-Programm
==============================

Läuft automatisch jede Stunde über GitHub Actions und

  1. fragt die Jobsuche der Bundesagentur für Arbeit ab, und zwar für jeden
     Suchbegriff, jede Region und jede Anstellungsart aus einstellungen.toml,
  2. behält nur Stellen, deren Titel zu einem deiner Bereiche passt,
  3. erkennt aus dem Titel die Karrierestufe (Berufseinstieg, Senior, Manager …),
  4. entfernt Dubletten und merkt sich, wann eine Stelle zum ersten Mal
     aufgetaucht ist (daraus entsteht die Sortierung "neueste zuerst"),
  5. speichert alles in jobs.json, die von der Webseite angezeigt wird.

Benötigt nur Python 3.11 oder neuer, keine Zusatzpakete.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import sys
import time
import tomllib
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from datetime import date, datetime, timedelta, timezone
from pathlib import Path

try:
    from zoneinfo import ZoneInfo

    BERLIN = ZoneInfo("Europe/Berlin")
except Exception:  # Zeitzonendaten fehlen: dann eben UTC
    BERLIN = timezone.utc

ORDNER = Path(__file__).resolve().parent
EINSTELLUNGEN = ORDNER / "einstellungen.toml"
DATENDATEI = ORDNER / "jobs.json"

# --- Bundesagentur für Arbeit ------------------------------------------------

BA_NAME = "Arbeitsagentur"
BA_BASIS = "https://rest.arbeitsagentur.de/jobboerse/jobsuche-service"
# Die BA hat mehrere Versionen der Suche. Die erste, die antwortet, wird benutzt.
BA_ENDPUNKTE = ["/pc/v6/jobs", "/pc/v4/app/jobs", "/pc/v4/jobs"]
BA_DETAILSEITE = "https://www.arbeitsagentur.de/jobsuche/jobdetail/{refnr}"
BA_HEADER = {
    "X-API-Key": "jobboerse-jobsuche",  # öffentlicher Schlüssel der BA-Jobsuche
    "Accept": "application/json",
    "User-Agent": "Stellenradar/1.1 (privates Bewerbungsportal)",
}

# Jede Suche läuft dreimal: einmal je Anstellungsart. Daran erkennen wir,
# ob eine Stelle Vollzeit, Teilzeit oder ein Praktikum ist.
ABFRAGE_ARTEN = [
    ("Vollzeit", {"angebotsart": 1, "arbeitszeit": "vz"}),
    ("Teilzeit", {"angebotsart": 1, "arbeitszeit": "tz"}),
    ("Praktikum", {"angebotsart": 34}),  # 34 = Praktikum/Trainee
]
SEITENGROESSE = 100
MAX_SEITEN = 10
PAUSE_SEKUNDEN = 0.25

# Diese Wörter im Titel legen die Anstellungsart genauer fest.
ART_MUSTER = {
    "Werkstudent": ["werkstudent", "working student", "studentische"],
    "Abschlussarbeit": ["abschlussarbeit", "masterarbeit", "bachelorarbeit", "thesis"],
    "Trainee": ["trainee", "graduate program", "absolventenprogramm"],
    "Praktikum": ["praktikum", "praktikant", "internship"],
}

# --- Karrierestufen --------------------------------------------------------------
#
# Die Stufe wird aus dem Stellentitel gelesen. Der Titel wird an "/", "|", ","
# und " - " in Teile zerlegt; für jeden Teil gilt die ERSTE passende Regel.
# "(Senior) Consultant" bedeutet beide Stufen: Berufseinstieg und Senior.

STUFEN = ["Berufseinstieg", "Senior", "Manager", "Director & Partner"]
OHNE_STUFE = "Ohne Angabe"
STUDENTISCHE_ARTEN = {"Praktikum", "Werkstudent", "Abschlussarbeit", "Trainee"}

STUFEN_REGELN = [
    # Eindeutige Hinweise auf den Einstieg haben Vorrang ("Junior Manager" = Einstieg)
    ("Berufseinstieg", r"\b(?:junior|jr)\b|berufseinst|einsteiger|berufsanfaeng|absolvent|"
                       r"\bgraduate|young professional|entry level|trainee|werkstudent|"
                       r"working student|praktik|internship|pruefungsassist|revisionsassist|"
                       r"berufsbegleitend"),
    # Sonderfälle vor "Manager": Assistant Manager, Prüfungsleiter, fachliche Manager-Titel
    ("Senior", r"assistant manager|pruefungsleit|\b(?:investment|portfolio|fund|asset|"
               r"business development|account|relationship|risk|product|projekt|project|"
               r"credit|kredit|office|quality)\s?manager"),
    # "Assistant/Associate Director" liegt zwischen Manager und Director
    ("Manager", r"(?:assistant|associate) director"),
    ("Director & Partner", r"\bpartner(?:in)?\b|\bdirector\b|\bdirektor(?:in)?\b|head of|"
                           r"\bleiter(?:in)?\b|\bleitung\b|abteilungsleit|bereichsleit|"
                           r"geschaeftsfuehr|vice president|\bvp\b|\bprincipal\b|\bchief\b"),
    ("Manager", r"\bmanager(?:in)?\b|teamleit|gruppenleit|projektleit|team lead"),
    ("Senior", r"\bsenior\b|\bsnr\b|\bsr\b|referent|spezialist|specialist|experienced|"
               r"erfahren|\bexpert|\bwirtschaftspruefer(?:in)?\b|\bsteuerberater(?:in)?\b|"
               r"\brevisor(?:in)?\b"),
    ("Berufseinstieg", r"\bassociate\b|\bconsultant\b|\banalyst\b|\bassistant\b|assistent"),
]
_STUFEN_REGELN = [(stufe, re.compile(muster)) for stufe, muster in STUFEN_REGELN]
_OPTIONAL_SENIOR = re.compile(r"\(\s*(?:senior|sr|snr)\.?\s*-?\s*\)")
_OPTIONAL_JUNIOR = re.compile(r"\(\s*(?:junior|jr)\.?\s*-?\s*\)")
_JUNIOR_SENIOR = re.compile(r"\b(?:junior|jr)\.?\s*/\s*(?:senior|sr|snr)\b\.?|"
                            r"\b(?:senior|sr|snr)\.?\s*/\s*(?:junior|jr)\b\.?")
_TITELTEILE = re.compile(r"\s*[/|,;]\s*|\s+[-–—]\s+|\s+(?:oder|bzw\.?|or)\s+")

# Geschlechtsangaben wie (m/w/d) werden aus dem Titel entfernt.
GENDER_MUSTER = re.compile(
    r"\(\s*(?:[mwfdxi]\s*[/|,]?\s*){2,4}\)"
    r"|\(\s*(?:all genders|alle geschlechter|gn\*?|m/w/d|w/m/d)\s*\)"
    r"|\b(?:m|w|d)\s*/\s*(?:m|w|d)\s*/\s*(?:m|w|d|x)\b",
    re.IGNORECASE,
)


# --- Hilfsfunktionen ---------------------------------------------------------


def umlaute(text: str) -> str:
    t = (text or "").lower()
    for alt, neu in (("ä", "ae"), ("ö", "oe"), ("ü", "ue"), ("ß", "ss")):
        t = t.replace(alt, neu)
    return t


def normalisiere(text: str) -> str:
    """Kleinbuchstaben, Umlaute ausgeschrieben, Satzzeichen als Leerzeichen."""
    t = re.sub(r"[-_/|,;:()\[\]{}.\"'+*!?–—]", " ", umlaute(text))
    return re.sub(r"\s+", " ", t).strip()


def bereinige_titel(titel: str) -> str:
    t = GENDER_MUSTER.sub(" ", titel or "")
    t = re.sub(r"\s+", " ", t).strip()
    return re.sub(r"[\s\-–—|,:/]+$", "", t).strip()


def erstes(daten: dict, *schluessel):
    """Erster vorhandene Wert aus mehreren möglichen Feldnamen."""
    for s in schluessel:
        wert = daten.get(s)
        if wert not in (None, "", [], {}):
            return wert
    return None


def suche_tief(wert, schluessel: tuple, tiefe: int = 0):
    """Sucht in verschachtelten Daten den ersten Wert zu einem der Feldnamen."""
    if tiefe > 4:
        return None
    if isinstance(wert, dict):
        for s in schluessel:
            v = wert.get(s)
            if isinstance(v, (str, int, float)) and str(v).strip():
                return v
        for v in wert.values():
            if isinstance(v, (dict, list)):
                gefunden = suche_tief(v, schluessel, tiefe + 1)
                if gefunden not in (None, ""):
                    return gefunden
    elif isinstance(wert, list):
        for v in wert:
            gefunden = suche_tief(v, schluessel, tiefe + 1)
            if gefunden not in (None, ""):
                return gefunden
    return None


def als_datum(wert) -> date | None:
    """Liest ein Datum aus Text ("2026-10-15", "15.10.2026"), Zeitstempel oder {von: …}."""
    if wert in (None, "", [], {}):
        return None
    if isinstance(wert, dict):
        for s in ("von", "beginn", "start", "ab", "datum"):
            if wert.get(s):
                return als_datum(wert[s])
        return None
    if isinstance(wert, list):
        return als_datum(wert[0])
    if isinstance(wert, (int, float)) and wert > 10**11:  # Millisekunden seit 1970
        return datetime.fromtimestamp(wert / 1000, tz=timezone.utc).date()
    text = str(wert).strip()
    try:
        return date.fromisoformat(text[:10])
    except ValueError:
        pass
    treffer = re.match(r"(\d{1,2})\.(\d{1,2})\.(\d{4})", text)
    if treffer:
        try:
            return date(int(treffer[3]), int(treffer[2]), int(treffer[1]))
        except ValueError:
            return None
    return None


def als_zahl(wert, ersatz: int = 0) -> int:
    try:
        return int(str(wert).strip())
    except (TypeError, ValueError):
        return ersatz


def kurz_id(text: str) -> str:
    return "ba-" + hashlib.sha1(text.encode("utf-8")).hexdigest()[:12]


# --- Einstellungen und alte Daten ----------------------------------------------


def lade_einstellungen() -> dict:
    with EINSTELLUNGEN.open("rb") as f:
        roh = tomllib.load(f)

    allgemein = roh.get("allgemein", {})
    regionen = [
        {
            "name": str(r["name"]),
            "ort": str(r["ort"]),
            "umkreis": int(r.get("umkreis_km", 25)),
        }
        for r in roh.get("region", [])
    ]
    begriffe = [str(b) for b in roh.get("suche", {}).get("begriffe", []) if str(b).strip()]

    # Je Bereich die Stichwörter normalisieren, längste zuerst prüfen.
    bereiche = []
    for name, woerter in roh.get("bereiche", {}).items():
        norm = sorted({normalisiere(w) for w in woerter if normalisiere(w)}, key=len, reverse=True)
        bereiche.append((name, norm))

    ausschluss = [normalisiere(w) for w in roh.get("ausschluss", {}).get("woerter", [])]

    if not regionen or not begriffe or not bereiche:
        sys.exit("einstellungen.toml braucht mindestens eine Region, einen Suchbegriff und einen Bereich.")

    return {
        "max_alter": max(1, min(100, int(allgemein.get("max_alter_tage", 60)))),
        "ohne_pav": bool(allgemein.get("ohne_personalvermittlung", True)),
        "ohne_zeitarbeit": bool(allgemein.get("ohne_zeitarbeit", True)),
        "regionen": regionen,
        "begriffe": begriffe,
        "bereiche": bereiche,
        "ausschluss": [w for w in ausschluss if w],
    }


def lade_alte_daten() -> dict:
    try:
        return json.loads(DATENDATEI.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


# --- Einordnung ----------------------------------------------------------------


def finde_bereiche(text: str, bereiche: list) -> list[str]:
    """Bereiche in Vorrang-Reihenfolge; erkannte Wörter werden 'verbraucht'."""
    rest = f" {text} "
    treffer = []
    for name, woerter in bereiche:
        gefunden = False
        for wort in woerter:
            if wort in rest:
                gefunden = True
                rest = rest.replace(wort, " ")
        if gefunden:
            treffer.append(name)
    return treffer


def bestimme_arten(arten: set[str], titel_norm: str) -> list[str]:
    def hat(art: str) -> bool:
        return any(normalisiere(m) in titel_norm for m in ART_MUSTER[art])

    if hat("Werkstudent"):
        return ["Werkstudent"]
    if hat("Abschlussarbeit"):
        return ["Abschlussarbeit"]
    if hat("Praktikum"):
        return ["Praktikum"]
    ergebnis = set(arten)
    if hat("Trainee"):
        ergebnis.discard("Praktikum")
        ergebnis.add("Trainee")
    reihenfolge = ["Vollzeit", "Teilzeit", "Trainee", "Praktikum"]
    return [a for a in reihenfolge if a in ergebnis]


def bestimme_stufen(titel: str, arten: list[str]) -> list[str]:
    """Karrierestufe(n) aus dem Titel; Praktika & Co. zählen als Berufseinstieg."""
    if STUDENTISCHE_ARTEN & set(arten):
        return ["Berufseinstieg"]

    t = umlaute(titel)
    zusatz = set()
    if _OPTIONAL_SENIOR.search(t):  # "(Senior) Consultant"
        zusatz.add("Senior")
        t = _OPTIONAL_SENIOR.sub(" ", t)
    if _OPTIONAL_JUNIOR.search(t):  # "(Junior) Consultant"
        zusatz.add("Berufseinstieg")
        t = _OPTIONAL_JUNIOR.sub(" ", t)
    beide = _JUNIOR_SENIOR.search(t)  # "Junior/Senior Consultant"
    if beide:
        zusatz |= {"Berufseinstieg", "Senior"}
        t = t.replace(beide.group(0), " ")

    stufen = set()
    for teil in _TITELTEILE.split(t):
        text = normalisiere(teil)
        if not text:
            continue
        for stufe, muster in _STUFEN_REGELN:
            if muster.search(text):
                stufen.add(stufe)
                break

    # "(Senior) Manager" bleibt Manager; "(Senior) Consultant" wird Einstieg + Senior.
    if "Senior" in zusatz and stufen & {"Manager", "Director & Partner"}:
        zusatz.discard("Senior")
    stufen |= zusatz
    return [s for s in STUFEN if s in stufen] or [OHNE_STUFE]


# --- Abruf bei der Arbeitsagentur ------------------------------------------------


def hole_json(url: str, parameter: dict, versuche: int = 4):
    abfrage = urllib.parse.urlencode(
        {k: str(v) for k, v in parameter.items()}, quote_via=urllib.parse.quote, safe=";"
    )
    anfrage = urllib.request.Request(f"{url}?{abfrage}", headers=BA_HEADER)
    for versuch in range(1, versuche + 1):
        try:
            with urllib.request.urlopen(anfrage, timeout=30) as antwort:
                return json.load(antwort)
        except urllib.error.HTTPError as fehler:
            nochmal = fehler.code in (429, 500, 502, 503, 504)
            if not nochmal or versuch == versuche:
                raise
        except (urllib.error.URLError, TimeoutError, ConnectionError, json.JSONDecodeError):
            if versuch == versuche:
                raise
        time.sleep(3 * 2 ** (versuch - 1))  # 3 s, 6 s, 12 s


def stellen_liste(antwort) -> list | None:
    if not isinstance(antwort, dict):
        return None
    for schluessel in ("stellenangebote", "ergebnisse", "stellen", "jobs", "content"):
        wert = antwort.get(schluessel)
        if isinstance(wert, list):
            return wert
    for wert in antwort.values():
        if isinstance(wert, list) and wert and isinstance(wert[0], dict):
            if any(k in wert[0] for k in ("refnr", "referenznummer", "titel", "stellenangebotsTitel")):
                return wert
    return None


def sieht_aus_wie_suchantwort(antwort) -> bool:
    if not isinstance(antwort, dict):
        return False
    bekannte = {"stellenangebote", "maxErgebnisse", "facetten", "page", "size", "ergebnisse"}
    return bool(bekannte & set(antwort)) or stellen_liste(antwort) is not None


def referenz(roh) -> str | None:
    return erstes(roh, "refnr", "referenznummer", "refNr") if isinstance(roh, dict) else None


def finde_endpunkt(protokoll: list, diagnose: dict) -> tuple[str | None, dict]:
    """Erste funktionierende Schnittstelle und ob ihre Seiten bei 0 oder 1 beginnen."""
    test = {"was": "Wirtschaftsprüfung", "wo": "Frankfurt am Main", "umkreis": 50,
            "angebotsart": 1, "size": 1}
    for pfad in BA_ENDPUNKTE:
        try:
            antwort = hole_json(BA_BASIS + pfad, {**test, "page": 1}, versuche=2)
        except Exception as fehler:  # noqa: BLE001 – jede Art von Fehler protokollieren
            protokoll.append(f"{pfad}: {fehler}")
            continue
        if not sieht_aus_wie_suchantwort(antwort):
            felder = ", ".join(list(antwort)[:10]) if isinstance(antwort, dict) else type(antwort).__name__
            protokoll.append(f"{pfad}: unerwartetes Antwortformat ({felder})")
            continue
        diagnose["antwort_felder"] = sorted(antwort)
        return pfad, pruefe_seitenzaehlung(pfad, test, antwort, diagnose)
    return None, {"start": 1, "sicher": True}


def pruefe_seitenzaehlung(pfad, test, antwort1, diagnose) -> dict:
    """Beginnt die Seitenzählung bei 0 oder bei 1? Liefert Seite 0 einen anderen
    Eintrag als Seite 1, ist es 0. Lehnt die Schnittstelle Seite 0 ab, ist es 1."""
    liste1 = stellen_liste(antwort1) or []
    try:
        liste0 = stellen_liste(hole_json(BA_BASIS + pfad, {**test, "page": 0}, versuche=1)) or []
    except Exception:  # noqa: BLE001 – Seite 0 abgelehnt
        seiten = {"start": 1, "sicher": True}
    else:
        if liste0 and (not liste1 or referenz(liste0[0]) != referenz(liste1[0])):
            seiten = {"start": 0, "sicher": True}
        else:
            seiten = {"start": 1, "sicher": bool(liste0 or liste1)}
    diagnose["seitenstart"] = seiten["start"]
    return seiten


def ort_aus(daten) -> tuple[list[str], str]:
    """Alle Ortsnamen (in Reihenfolge) und die erste Postleitzahl."""
    eintraege = daten if isinstance(daten, list) else [daten]
    orte, plz = [], ""
    for eintrag in eintraege:
        if isinstance(eintrag, str):
            name = eintrag.strip()
        else:
            name = str(suche_tief(eintrag, ("ort", "stadt", "ortsname", "gemeinde", "city")) or "").strip()
            if not plz:
                plz = str(suche_tief(eintrag, ("plz", "postleitzahl", "zip")) or "").strip()
        if name and name not in orte:
            orte.append(name)
    return orte, plz


def lies_stelle(roh: dict) -> dict | None:
    """Übersetzt einen Eintrag der BA (alte oder neue Schnittstelle) in unser Format."""
    refnr = referenz(roh)
    titel = erstes(roh, "titel", "stellenangebotsTitel", "stellenbezeichnung", "beruf", "hauptberuf")
    if not refnr or not titel:
        return None

    firma = erstes(roh, "arbeitgeber", "firma", "arbeitgeberName") or ""
    if isinstance(firma, dict):
        firma = erstes(firma, "name", "firmenname", "arbeitgeber") or ""

    beruf = erstes(roh, "beruf", "hauptberuf") or ""
    if isinstance(beruf, dict):
        beruf = erstes(beruf, "name", "bezeichnung", "kurzBezeichnung") or ""

    orte, plz = ort_aus(erstes(roh, "arbeitsort", "arbeitsorte", "stellenlokationen") or [])

    datum = (als_datum(erstes(roh, "datumErsteVeroeffentlichung", "ersteVeroeffentlichungsdatum"))
             or als_datum(erstes(roh, "aktuelleVeroeffentlichungsdatum", "veroeffentlichungsdatum"))
             or als_datum(roh.get("veroeffentlichungszeitraum"))
             or als_datum(erstes(roh, "aenderungsdatum", "modifikationsTimestamp")))

    extern = erstes(roh, "externeUrl")
    if not (isinstance(extern, str) and extern.startswith(("https://", "http://"))):
        extern = None

    return {
        "refnr": str(refnr),
        "titel": bereinige_titel(str(titel)),
        "beruf": str(beruf),
        "firma": str(firma).strip(),
        "orte": orte[:6],
        "plz": plz,
        "datum": datum,
        "extern": extern,
    }


def sammle_arbeitsagentur(cfg, statistik, beispiele, protokoll, diagnose):
    """Gibt (Rohtreffer nach Referenznummer, Abfragen, fehlgeschlagen, Endpunkt) zurück."""
    endpunkt, seiten = finde_endpunkt(protokoll, diagnose)
    if not endpunkt:
        return {}, 0, 0, None

    treffer: dict[str, dict] = {}
    abfragen = fehlgeschlagen = 0

    for region in cfg["regionen"]:
        for begriff in cfg["begriffe"]:
            for art, art_parameter in ABFRAGE_ARTEN:
                abfragen += 1
                parameter = {
                    "was": begriff,
                    "wo": region["ort"],
                    "umkreis": region["umkreis"],
                    "veroeffentlichtseit": cfg["max_alter"],
                    "size": SEITENGROESSE,
                    "pav": "false" if cfg["ohne_pav"] else "true",
                    "zeitarbeit": "false" if cfg["ohne_zeitarbeit"] else "true",
                    **art_parameter,
                }
                try:
                    for nummer in range(MAX_SEITEN):
                        parameter["page"] = seiten["start"] + nummer
                        antwort = hole_json(BA_BASIS + endpunkt, parameter)
                        time.sleep(PAUSE_SEKUNDEN)
                        liste = stellen_liste(antwort) or []
                        if not liste and nummer == 0 and not seiten["sicher"] and seiten["start"] == 1:
                            # Seitenzählung noch unklar: Seite 0 probieren
                            seiten = pruefe_seitenzaehlung(endpunkt, {**parameter, "size": SEITENGROESSE},
                                                           antwort, diagnose)
                            if seiten["start"] == 0:
                                parameter["page"] = 0
                                antwort = hole_json(BA_BASIS + endpunkt, parameter)
                                liste = stellen_liste(antwort) or []
                        if liste and "beispiele_roh" not in diagnose:
                            diagnose["beispiele_roh"] = liste[:2]
                            beispiele["felder"] = sorted(liste[0].keys())
                        for roh in liste:
                            if isinstance(roh, dict):
                                verarbeite(roh, region["name"], art, cfg, treffer, statistik, beispiele)
                        gesamt = als_zahl(antwort.get("maxErgebnisse"), 0) if isinstance(antwort, dict) else 0
                        if len(liste) < SEITENGROESSE or (gesamt and (nummer + 1) * SEITENGROESSE >= gesamt):
                            break
                except Exception as fehler:  # noqa: BLE001
                    fehlgeschlagen += 1
                    if len(protokoll) < 20:
                        protokoll.append(f"{begriff} / {region['name']} / {art}: {fehler}")

    return treffer, abfragen, fehlgeschlagen, endpunkt


def verarbeite(roh, region, art, cfg, treffer, statistik, beispiele):
    stelle = lies_stelle(roh)
    if not stelle:
        statistik["unlesbar"] += 1
        return
    titel_norm = normalisiere(stelle["titel"])

    # Die Ausschlussliste gilt für den Titel. Den von der BA zugeordneten Beruf
    # prüfen wir nur, wenn der Titel allein keinen Bereich ergibt – die Zuordnung
    # der BA ist oft ungenau (z. B. "Internal Auditor" als Qualitäts-Auditor).
    if any(w in titel_norm for w in cfg["ausschluss"]):
        beispiele["ausgeschlossen"][stelle["titel"]] += 1
        return

    bereiche = finde_bereiche(titel_norm, cfg["bereiche"])
    if not bereiche and stelle["beruf"]:
        beruf_norm = normalisiere(stelle["beruf"])
        if any(w in beruf_norm for w in cfg["ausschluss"]):
            beispiele["ausgeschlossen"][stelle["titel"]] += 1
            return
        bereiche = finde_bereiche(beruf_norm, cfg["bereiche"])
    if not bereiche:
        beispiele["kein_bereich"][stelle["titel"]] += 1
        return

    eintrag = treffer.get(stelle["refnr"])
    if eintrag is None:
        eintrag = {**stelle, "bereiche": bereiche, "regionen": set(), "abfrage_arten": set()}
        treffer[stelle["refnr"]] = eintrag
    eintrag["regionen"].add(region)
    eintrag["abfrage_arten"].add(art)


# --- Zusammenführen und Speichern ------------------------------------------------


def signatur(titel: str, firma: str, ort: str) -> str:
    return "|".join(normalisiere(x) for x in (titel, firma, ort))


def fuehre_zusammen(treffer, alte_stellen, status, jetzt, heute, cfg):
    """Neue Treffer mit dem letzten Stand verbinden; liefert (stellen, anzahl_neu)."""
    erster_lauf = not alte_stellen
    region_reihenfolge = [r["name"] for r in cfg["regionen"]]

    # Dieselbe Stelle mehrfach veröffentlicht (gleicher Titel, Firma, Ort)? Zusammenfassen.
    gruppen: dict[str, list[dict]] = {}
    for e in treffer.values():
        gruppen.setdefault(signatur(e["titel"], e["firma"], e["orte"][0] if e["orte"] else ""), []).append(e)

    stellen = {}
    neu = 0
    for gruppe in gruppen.values():
        ids = sorted(kurz_id(e["refnr"]) for e in gruppe)
        sid = next((i for i in ids if i in alte_stellen), ids[0])  # bekannte ID behalten
        neueste = max(gruppe, key=lambda e: e["datum"] or date.min)
        aelteste = min((e["datum"] for e in gruppe if e["datum"]), default=None)
        datum = aelteste or heute

        regionen = set().union(*(e["regionen"] for e in gruppe))
        abfrage_arten = set().union(*(e["abfrage_arten"] for e in gruppe))
        orte = []
        for e in gruppe:
            orte += [o for o in e["orte"] if o not in orte]
        arten = bestimme_arten(abfrage_arten, normalisiere(neueste["titel"]))

        stelle = {
            "id": sid,
            "titel": neueste["titel"],
            "firma": neueste["firma"],
            "ort": orte[0] if orte else "",
            "plz": neueste["plz"],
            "regionen": [r for r in region_reihenfolge if r in regionen],
            "bereiche": neueste["bereiche"],
            "arten": arten,
            "stufen": bestimme_stufen(neueste["titel"], arten),
            "veroeffentlicht": datum.isoformat(),
            "link": BA_DETAILSEITE.format(refnr=urllib.parse.quote(neueste["refnr"])),
            "quelle": BA_NAME,
        }
        if len(orte) > 1:
            stelle["weitere_orte"] = orte[1:6]
        extern = neueste["extern"] or next((e["extern"] for e in gruppe if e["extern"]), None)
        if extern:
            stelle["extern"] = extern

        # Bisherigen Eintrag finden: über die ID oder (Übergang von Version 1.0)
        # über die alte ID aus Titel und Firma ohne Ort.
        alte_id = kurz_id(f"{normalisiere(neueste['titel'])}|{normalisiere(neueste['firma'])}|")
        alt = alte_stellen.get(sid) or alte_stellen.get(alte_id)
        frueher = set((alt or {}).get("alt", []))
        if alte_id in alte_stellen and alte_id != sid:
            frueher.add(alte_id)
        if frueher:
            stelle["alt"] = sorted(frueher)

        if alt and alt.get("gesehen"):
            if alt.get("genau"):
                stelle["gesehen"], stelle["genau"] = alt["gesehen"], True
            else:
                # Nur Datum bekannt: das Veröffentlichungsdatum zählt (das frühere von beiden).
                stelle["gesehen"] = min(str(alt["gesehen"])[:10], datum.isoformat())
                stelle["genau"] = False
        else:
            neu += 1
            if erster_lauf or datum < heute - timedelta(days=1):
                # Ältere Anzeige: Uhrzeit unbekannt, nur das Datum zählt
                stelle["gesehen"], stelle["genau"] = datum.isoformat(), False
            else:
                stelle["gesehen"], stelle["genau"] = jetzt.isoformat().replace("+00:00", "Z"), True
        stellen[sid] = stelle

    if status != "ok":
        # Wenn Abfragen fehlgeschlagen sind, nichts löschen – nur ergänzen,
        # aber keine uralten Einträge mitschleppen.
        grenze = (heute - timedelta(days=cfg["max_alter"] + 14)).isoformat()
        uebernommen = {i for s in stellen.values() for i in s.get("alt", [])}
        for sid, alt in alte_stellen.items():
            if sid not in stellen and sid not in uebernommen and str(alt.get("gesehen", ""))[:10] >= grenze:
                stellen[sid] = alt
    return stellen, neu


def schreibe_daten(daten: dict) -> None:
    """Eine Stelle pro Zeile, sortiert – so bleiben die Änderungen bei GitHub klein."""
    kopf = {k: v for k, v in daten.items() if k not in ("stellen", "diagnose")}
    zeilen = ["{"]
    for k, v in kopf.items():
        zeilen.append(f"  {json.dumps(k)}: {json.dumps(v, ensure_ascii=False, sort_keys=True)},")
    if "diagnose" in daten:
        zeilen.append(f'  "diagnose": {json.dumps(daten["diagnose"], ensure_ascii=False, sort_keys=True)},')
    stellen = sorted(daten["stellen"], key=lambda s: s["id"])
    zeilen.append('  "stellen": [')
    for i, s in enumerate(stellen):
        komma = "," if i < len(stellen) - 1 else ""
        zeilen.append("    " + json.dumps(s, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + komma)
    zeilen.append("  ]")
    zeilen.append("}")
    DATENDATEI.write_text("\n".join(zeilen) + "\n", encoding="utf-8")


def berichte(zeilen: list[str], status: str) -> None:
    text = "\n".join(zeilen)
    print(text)
    zusammenfassung = os.environ.get("GITHUB_STEP_SUMMARY")
    if zusammenfassung:
        with open(zusammenfassung, "a", encoding="utf-8") as f:
            f.write(text + "\n")
    ausgabe = os.environ.get("GITHUB_OUTPUT")
    if ausgabe:
        with open(ausgabe, "a", encoding="utf-8") as f:
            f.write(f"status={status}\n")


def main() -> None:
    cfg = lade_einstellungen()
    jetzt = datetime.now(timezone.utc).replace(microsecond=0)
    heute = jetzt.astimezone(BERLIN).date()

    alt = lade_alte_daten()
    alte_stellen = {s["id"]: s for s in alt.get("stellen", []) if isinstance(s, dict) and s.get("id")}
    alte_quelle = (alt.get("quellen") or {}).get(BA_NAME, {})

    statistik: Counter = Counter()
    beispiele: dict = {"kein_bereich": Counter(), "ausgeschlossen": Counter()}
    protokoll: list[str] = []
    diagnose: dict = {}
    start = time.monotonic()

    treffer, abfragen, fehlgeschlagen, endpunkt = sammle_arbeitsagentur(
        cfg, statistik, beispiele, protokoll, diagnose)

    if not endpunkt or abfragen == 0 or fehlgeschlagen == abfragen:
        status = "fehler"
    elif fehlgeschlagen:
        status = "teilweise"
    else:
        status = "ok"

    stellen, neu = fuehre_zusammen(treffer, alte_stellen, status, jetzt, heute, cfg)
    zeitstempel = jetzt.isoformat().replace("+00:00", "Z")

    ohne_ort = sum(1 for s in stellen.values() if not s.get("ort"))
    ohne_stufe = Counter(s["titel"] for s in stellen.values() if s.get("stufen") == [OHNE_STUFE])
    diagnose.update({
        "endpunkt": endpunkt,
        "ohne_ort": ohne_ort,
        "ohne_stufe": [t for t, _ in ohne_stufe.most_common(60)],
        "kein_bereich": [t for t, _ in beispiele["kein_bereich"].most_common(150)],
        "ausgeschlossen": [t for t, _ in beispiele["ausgeschlossen"].most_common(60)],
    })

    daten = {
        "version": 2,
        "stand": zeitstempel,
        "quellen": {
            BA_NAME: {
                "status": status,
                "abfragen": abfragen,
                "fehlgeschlagen": fehlgeschlagen,
                "letzter_erfolg": zeitstempel if status != "fehler" else alte_quelle.get("letzter_erfolg"),
            }
        },
        "bereiche": [name for name, _ in cfg["bereiche"]],
        "regionen": [r["name"] for r in cfg["regionen"]],
        "stufen": STUFEN + [OHNE_STUFE],
        "diagnose": diagnose,
        "stellen": list(stellen.values()),
    }
    if status == "fehler" and alt.get("diagnose"):
        daten["diagnose"] = {**alt["diagnose"], "letzter_fehler": protokoll[:5]}
    schreibe_daten(daten)

    # --- Bericht für das Protokoll bei GitHub ---
    dauer = time.monotonic() - start
    bereich_zahlen = Counter(b for s in stellen.values() for b in s["bereiche"])
    art_zahlen = Counter(a for s in stellen.values() for a in s["arten"])
    stufen_zahlen = Counter(x for s in stellen.values() for x in s.get("stufen", [OHNE_STUFE]))
    zeilen = [
        f"## Stellenradar – Lauf vom {jetzt.astimezone(BERLIN):%d.%m.%Y, %H:%M} Uhr",
        "",
        f"- Arbeitsagentur: **{status}** – {abfragen} Abfragen, {fehlgeschlagen} fehlgeschlagen, "
        f"Schnittstelle `{endpunkt or 'keine erreichbar'}`, Dauer {dauer:.0f} s",
        f"- Stellen im Radar: **{len(stellen)}**, davon neu in diesem Lauf: **{neu}**, ohne Ortsangabe: {ohne_ort}",
        f"- Verworfene Titel: {len(beispiele['kein_bereich'])} ohne passenden Bereich, "
        f"{len(beispiele['ausgeschlossen'])} durch die Ausschlussliste, {statistik['unlesbar']} unlesbare Einträge",
        "- Nach Bereich: " + (", ".join(f"{b} {n}" for b, n in bereich_zahlen.most_common()) or "–"),
        "- Nach Anstellungsart: " + (", ".join(f"{a} {n}" for a, n in art_zahlen.most_common()) or "–"),
        "- Nach Karrierestufe: " + (", ".join(f"{a} {n}" for a, n in stufen_zahlen.most_common()) or "–"),
    ]
    if beispiele.get("felder"):
        zeilen.append("- Felder der Schnittstelle: " + ", ".join(beispiele["felder"]))
    for schluessel, ueberschrift in (("kein_bereich", "Häufigste Titel ohne passenden Bereich"),
                                      ("ausgeschlossen", "Häufigste durch die Ausschlussliste verworfene Titel")):
        if beispiele[schluessel]:
            zeilen.append(f"- {ueberschrift}: " + "; ".join(t for t, _ in beispiele[schluessel].most_common(12)))
    if protokoll:
        zeilen += ["", "**Hinweise:**"] + [f"- {p}" for p in protokoll]
    berichte(zeilen, status)

    if status == "fehler":
        print("::warning::Die Arbeitsagentur konnte nicht abgefragt werden. Die bisherigen Stellen bleiben erhalten.")
    elif status == "teilweise":
        print(f"::warning::{fehlgeschlagen} von {abfragen} Abfragen sind fehlgeschlagen.")


if __name__ == "__main__":
    main()
