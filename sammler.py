#!/usr/bin/env python3
"""
Stellenradar – Sammel-Programm
==============================

Läuft automatisch jede Stunde über GitHub Actions und

  1. fragt die Jobsuche der Bundesagentur für Arbeit ab, und zwar für jeden
     Suchbegriff, jede Region und jede Anstellungsart aus einstellungen.toml,
  2. behält nur Stellen, deren Titel zu einem deiner Bereiche passt,
  3. entfernt Dubletten und merkt sich, wann eine Stelle zum ersten Mal
     aufgetaucht ist (daraus entsteht die Sortierung "neueste zuerst"),
  4. speichert alles in jobs.json, die von der Webseite angezeigt wird.

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
BA_ENDPUNKTE = ["/pc/v4/app/jobs", "/pc/v6/jobs", "/pc/v4/jobs"]
BA_DETAILSEITE = "https://www.arbeitsagentur.de/jobsuche/jobdetail/{refnr}"
BA_HEADER = {
    "X-API-Key": "jobboerse-jobsuche",  # öffentlicher Schlüssel der BA-Jobsuche
    "Accept": "application/json",
    "User-Agent": "Stellenradar/1.0 (privates Bewerbungsportal)",
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

# Geschlechtsangaben wie (m/w/d) werden aus dem Titel entfernt.
GENDER_MUSTER = re.compile(
    r"\(\s*(?:[mwfdxi]\s*[/|,]?\s*){2,4}\)"
    r"|\(\s*(?:all genders|alle geschlechter|gn\*?|m/w/d|w/m/d)\s*\)"
    r"|\b(?:m|w|d)\s*/\s*(?:m|w|d)\s*/\s*(?:m|w|d|x)\b",
    re.IGNORECASE,
)


# --- Hilfsfunktionen ---------------------------------------------------------


def normalisiere(text: str) -> str:
    """Kleinbuchstaben, Umlaute ausgeschrieben, Satzzeichen als Leerzeichen."""
    t = (text or "").lower()
    for alt, neu in (("ä", "ae"), ("ö", "oe"), ("ü", "ue"), ("ß", "ss")):
        t = t.replace(alt, neu)
    t = re.sub(r"[-_/|,;:()\[\]{}.\"'+*!?–—]", " ", t)
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


def als_datum(wert) -> date | None:
    try:
        return date.fromisoformat(str(wert)[:10])
    except (TypeError, ValueError):
        return None


def als_zahl(wert, ersatz: int = 0) -> int:
    try:
        return int(str(wert).strip())
    except (TypeError, ValueError):
        return ersatz


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
            if any(k in wert[0] for k in ("refnr", "referenznummer", "titel")):
                return wert
    return None


def sieht_aus_wie_suchantwort(antwort) -> bool:
    if not isinstance(antwort, dict):
        return False
    bekannte = {"stellenangebote", "maxErgebnisse", "facetten", "page", "size", "ergebnisse"}
    return bool(bekannte & set(antwort)) or stellen_liste(antwort) is not None


def finde_endpunkt(protokoll: list) -> str | None:
    test = {"was": "Wirtschaftsprüfung", "wo": "Frankfurt am Main", "umkreis": 25,
            "angebotsart": 1, "page": 1, "size": 1}
    for pfad in BA_ENDPUNKTE:
        try:
            antwort = hole_json(BA_BASIS + pfad, test, versuche=2)
        except Exception as fehler:  # noqa: BLE001 – jede Art von Fehler protokollieren
            protokoll.append(f"{pfad}: {fehler}")
            continue
        if sieht_aus_wie_suchantwort(antwort):
            return pfad
        felder = ", ".join(list(antwort)[:10]) if isinstance(antwort, dict) else type(antwort).__name__
        protokoll.append(f"{pfad}: unerwartetes Antwortformat ({felder})")
    return None


def lies_stelle(roh: dict) -> dict | None:
    """Übersetzt einen Eintrag der BA in unser einheitliches Format."""
    refnr = erstes(roh, "refnr", "referenznummer", "refNr")
    titel = erstes(roh, "titel", "stellenangebotsTitel", "stellenbezeichnung", "beruf")
    if not refnr or not titel:
        return None

    firma = erstes(roh, "arbeitgeber", "arbeitgeberName", "firma") or ""
    if isinstance(firma, dict):
        firma = erstes(firma, "name", "firmenname", "arbeitgeber") or ""

    ort_daten = erstes(roh, "arbeitsort", "arbeitsorte") or {}
    if isinstance(ort_daten, list):
        ort_daten = ort_daten[0] if ort_daten else {}
    if not isinstance(ort_daten, dict):
        ort_daten = {}

    datum = als_datum(erstes(roh, "aktuelleVeroeffentlichungsdatum",
                             "veroeffentlichungsdatum", "ersteVeroeffentlichungsdatum"))
    extern = erstes(roh, "externeUrl")
    if not (isinstance(extern, str) and extern.startswith(("https://", "http://"))):
        extern = None

    return {
        "refnr": str(refnr),
        "titel": bereinige_titel(str(titel)),
        "beruf": str(erstes(roh, "beruf") or ""),
        "firma": str(firma).strip(),
        "ort": str(erstes(ort_daten, "ort", "stadt") or "").strip(),
        "plz": str(erstes(ort_daten, "plz") or "").strip(),
        "datum": datum,
        "extern": extern,
    }


def sammle_arbeitsagentur(cfg: dict, statistik: Counter, beispiele: dict, protokoll: list):
    """Gibt (Stellen nach ID, Anzahl Abfragen, Anzahl fehlgeschlagen, Endpunkt) zurück."""
    endpunkt = finde_endpunkt(protokoll)
    if not endpunkt:
        return {}, 0, 0, None

    gefunden: dict[str, dict] = {}
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
                    for seite in range(1, MAX_SEITEN + 1):
                        parameter["page"] = seite
                        antwort = hole_json(BA_BASIS + endpunkt, parameter)
                        time.sleep(PAUSE_SEKUNDEN)
                        liste = stellen_liste(antwort) or []
                        if liste and "felder" not in beispiele:
                            beispiele["felder"] = sorted(liste[0].keys())
                        for roh in liste:
                            if isinstance(roh, dict):
                                verarbeite(roh, region["name"], art, cfg, gefunden, statistik, beispiele)
                        gesamt = als_zahl(antwort.get("maxErgebnisse"), 0) if isinstance(antwort, dict) else 0
                        if len(liste) < SEITENGROESSE or (gesamt and seite * SEITENGROESSE >= gesamt):
                            break
                except Exception as fehler:  # noqa: BLE001
                    fehlgeschlagen += 1
                    if len(protokoll) < 20:
                        protokoll.append(f"{begriff} / {region['name']} / {art}: {fehler}")

    return gefunden, abfragen, fehlgeschlagen, endpunkt


def verarbeite(roh, region, art, cfg, gefunden, statistik, beispiele):
    stelle = lies_stelle(roh)
    if not stelle:
        statistik["unlesbar"] += 1
        return
    titel_norm = normalisiere(stelle["titel"])
    pruef_text = f"{titel_norm} {normalisiere(stelle['beruf'])}"

    if any(w in pruef_text for w in cfg["ausschluss"]):
        statistik["ausgeschlossen"] += 1
        beispiele.setdefault("ausgeschlossen", set()).add(stelle["titel"])
        return

    bereiche = finde_bereiche(titel_norm, cfg["bereiche"])
    if not bereiche and stelle["beruf"]:
        bereiche = finde_bereiche(normalisiere(stelle["beruf"]), cfg["bereiche"])
    if not bereiche:
        statistik["kein_bereich"] += 1
        beispiele.setdefault("kein_bereich", set()).add(stelle["titel"])
        return

    signatur = "|".join(normalisiere(x) for x in (stelle["titel"], stelle["firma"], stelle["ort"]))
    sid = "ba-" + hashlib.sha1(signatur.encode("utf-8")).hexdigest()[:12]

    eintrag = gefunden.get(sid)
    if eintrag is None:
        eintrag = {**stelle, "id": sid, "regionen": set(), "abfrage_arten": set(), "bereiche": bereiche}
        gefunden[sid] = eintrag
    elif stelle["datum"] and (not eintrag["datum"] or stelle["datum"] > eintrag["datum"]):
        # Doppelt veröffentlicht: die aktuellste Anzeige verlinken
        eintrag.update(refnr=stelle["refnr"], datum=stelle["datum"], extern=stelle["extern"] or eintrag["extern"])
    eintrag["regionen"].add(region)
    eintrag["abfrage_arten"].add(art)


# --- Zusammenführen und Speichern ------------------------------------------------


def fuehre_zusammen(gefunden, alte_stellen, status, jetzt, heute, cfg):
    """Neue Daten mit dem letzten Stand verbinden; liefert (stellen, anzahl_neu)."""
    erster_lauf = not alte_stellen
    region_reihenfolge = [r["name"] for r in cfg["regionen"]]
    stellen = {}
    neu = 0

    for sid, e in gefunden.items():
        datum = e["datum"] or heute
        stelle = {
            "id": sid,
            "titel": e["titel"],
            "firma": e["firma"],
            "ort": e["ort"],
            "plz": e["plz"],
            "regionen": [r for r in region_reihenfolge if r in e["regionen"]],
            "bereiche": e["bereiche"],
            "arten": bestimme_arten(e["abfrage_arten"], normalisiere(e["titel"])),
            "veroeffentlicht": datum.isoformat(),
            "link": BA_DETAILSEITE.format(refnr=urllib.parse.quote(e["refnr"])),
            "quelle": BA_NAME,
        }
        if e["extern"]:
            stelle["extern"] = e["extern"]

        alt = alte_stellen.get(sid)
        if alt and alt.get("gesehen"):
            stelle["gesehen"] = alt["gesehen"]
            stelle["genau"] = bool(alt.get("genau"))
        else:
            neu += 1
            if erster_lauf or datum < heute - timedelta(days=1):
                # Ältere Anzeige: Uhrzeit unbekannt, nur das Datum zählt
                stelle["gesehen"] = datum.isoformat()
                stelle["genau"] = False
            else:
                stelle["gesehen"] = jetzt.isoformat().replace("+00:00", "Z")
                stelle["genau"] = True
        stellen[sid] = stelle

    if status != "ok":
        # Wenn Abfragen fehlgeschlagen sind, nichts löschen – nur ergänzen.
        for sid, alt in alte_stellen.items():
            stellen.setdefault(sid, alt)

    grenze = (heute - timedelta(days=cfg["max_alter"] + 14)).isoformat()
    stellen = {k: v for k, v in stellen.items() if v.get("veroeffentlicht", "") >= grenze}
    return stellen, neu


def schreibe_daten(daten: dict) -> None:
    """Eine Stelle pro Zeile, sortiert – so bleiben die Änderungen bei GitHub klein."""
    kopf = {k: v for k, v in daten.items() if k != "stellen"}
    zeilen = ["{"]
    for k, v in kopf.items():
        zeilen.append(f"  {json.dumps(k)}: {json.dumps(v, ensure_ascii=False, sort_keys=True)},")
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
    beispiele: dict = {}
    protokoll: list[str] = []
    start = time.monotonic()

    gefunden, abfragen, fehlgeschlagen, endpunkt = sammle_arbeitsagentur(cfg, statistik, beispiele, protokoll)

    if not endpunkt or abfragen == 0 or fehlgeschlagen == abfragen:
        status = "fehler"
    elif fehlgeschlagen:
        status = "teilweise"
    else:
        status = "ok"

    stellen, neu = fuehre_zusammen(gefunden, alte_stellen, status, jetzt, heute, cfg)
    zeitstempel = jetzt.isoformat().replace("+00:00", "Z")

    daten = {
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
        "stellen": list(stellen.values()),
    }
    schreibe_daten(daten)

    # --- Bericht für das Protokoll bei GitHub ---
    dauer = time.monotonic() - start
    bereich_zahlen = Counter(b for s in stellen.values() for b in s["bereiche"])
    art_zahlen = Counter(a for s in stellen.values() for a in s["arten"])
    zeilen = [
        f"## Stellenradar – Lauf vom {jetzt.astimezone(BERLIN):%d.%m.%Y, %H:%M} Uhr",
        "",
        f"- Arbeitsagentur: **{status}** – {abfragen} Abfragen, {fehlgeschlagen} fehlgeschlagen, "
        f"Schnittstelle `{endpunkt or 'keine erreichbar'}`, Dauer {dauer:.0f} s",
        f"- Stellen im Radar: **{len(stellen)}**, davon neu in diesem Lauf: **{neu}**",
        f"- Verworfene Titel: {len(beispiele.get('kein_bereich', ()))} ohne passenden Bereich, "
        f"{len(beispiele.get('ausgeschlossen', ()))} durch die Ausschlussliste, {statistik['unlesbar']} unlesbare Einträge",
        "- Nach Bereich: " + (", ".join(f"{b} {n}" for b, n in bereich_zahlen.most_common()) or "–"),
        "- Nach Anstellungsart: " + (", ".join(f"{a} {n}" for a, n in art_zahlen.most_common()) or "–"),
    ]
    if beispiele.get("felder"):
        zeilen.append("- Felder der Schnittstelle: " + ", ".join(beispiele["felder"]))
    for schluessel, ueberschrift in (("kein_bereich", "Beispiele ohne passenden Bereich"),
                                      ("ausgeschlossen", "Beispiele durch Ausschlussliste verworfen")):
        if beispiele.get(schluessel):
            zeilen.append(f"- {ueberschrift}: " + "; ".join(sorted(beispiele[schluessel])[:15]))
    if protokoll:
        zeilen += ["", "**Hinweise:**"] + [f"- {p}" for p in protokoll]
    berichte(zeilen, status)

    if status == "fehler":
        print("::warning::Die Arbeitsagentur konnte nicht abgefragt werden. Die bisherigen Stellen bleiben erhalten.")
    elif status == "teilweise":
        print(f"::warning::{fehlgeschlagen} von {abfragen} Abfragen sind fehlgeschlagen.")


if __name__ == "__main__":
    main()
