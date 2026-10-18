#!/usr/bin/env python3
"""
Stellenradar – Sammel-Programm
==============================

Läuft automatisch jede Stunde über GitHub Actions und

  1. fragt die Jobsuche der Bundesagentur für Arbeit ab, und zwar für jeden
     Suchbegriff, jede Region und jede Anstellungsart aus einstellungen.toml,
  2. fragt die Karriereseiten der Firmen aus firmen.toml ab,
  3. behält nur Stellen, die zu deinen Bereichen und Regionen passen,
  4. erkennt aus dem Titel die Karrierestufe (Berufseinstieg, Senior, Manager …),
  5. entfernt Dubletten und merkt sich, wann eine Stelle zum ersten Mal
     aufgetaucht ist (daraus entsteht die Sortierung "neueste zuerst"),
  6. speichert alles in jobs.json, die von der Webseite angezeigt wird.

Benötigt nur Python 3.11 oder neuer, keine Zusatzpakete.
"""

from __future__ import annotations

import email.utils
import gzip
import hashlib
import html
import json
import os
import re
import sys
import time
import tomllib
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
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
FIRMENLISTE = ORDNER / "firmen.toml"
DATENDATEI = ORDNER / "jobs.json"

QUELLE_BA = "Arbeitsagentur"
QUELLE_FIRMA = "Karriereseite"

# --- Bundesagentur für Arbeit ------------------------------------------------

BA_NAME = QUELLE_BA
BA_BASIS = "https://rest.arbeitsagentur.de/jobboerse/jobsuche-service"
# Die BA hat mehrere Versionen der Suche. Die erste, die antwortet, wird benutzt.
BA_ENDPUNKTE = ["/pc/v6/jobs", "/pc/v4/app/jobs", "/pc/v4/jobs"]
BA_DETAILSEITE = "https://www.arbeitsagentur.de/jobsuche/jobdetail/{refnr}"
BA_HEADER = {
    "X-API-Key": "jobboerse-jobsuche",  # öffentlicher Schlüssel der BA-Jobsuche
    "Accept": "application/json",
    "User-Agent": "Stellenradar/1.3 (privates Bewerbungsportal)",
}
WEB_HEADER = {
    "User-Agent": "Mozilla/5.0 (compatible; Stellenradar/1.3; privates Bewerbungsportal)",
    "Accept-Language": "de-DE,de;q=0.9,en;q=0.8",
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
# So lange bleibt eine Stelle sichtbar, die eine erreichbare Quelle nicht mehr liefert
NACHFRIST_STUNDEN = 6

# Diese Wörter im Titel legen die Anstellungsart genauer fest.
ART_MUSTER = {
    "Werkstudent": re.compile(r"werkstudent|working student|studentische"),
    "Abschlussarbeit": re.compile(r"abschlussarbeit|masterarbeit|bachelorarbeit|thesis"),
    "Trainee": re.compile(r"trainee|graduate program|absolventenprogramm"),
    "Praktikum": re.compile(r"praktikum|praktikant|internship|\bintern\b|summer analyst|off cycle"),
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
                       r"working student|praktik|internship|\bintern\b|pruefungsassist|"
                       r"revisionsassist|berufsbegleitend"),
    # Sonderfälle vor "Manager": Assistant Manager, Prüfungsleiter, fachliche Manager-Titel
    ("Senior", r"assistant manager|pruefungsleit|\b(?:investment|portfolio|fund|asset|"
               r"business development|account|relationship|risk|product|projekt|project|"
               r"credit|kredit|office|quality)\s?manager"),
    # "Assistant/Associate Director" liegt zwischen Manager und Director
    ("Manager", r"(?:assistant|associate) director"),
    ("Director & Partner", r"\bpartner(?:in)?\b|\bdirector\b|\bdirektor(?:in)?\b|head of|"
                           r"\bleiter(?:in)?\b|\bleitung\b|abteilungsleit|bereichsleit|"
                           r"geschaeftsfuehr|vice president|\bvp\b|\bprincipal\b|\bchief\b"),
    ("Manager", r"\bmanager(?:in|s)?\b|teamleit|gruppenleit|projektleit|team lead"),
    ("Senior", r"\bseniors?\b|\bsnr\b|\bsr\b|referent|spezialist|specialist|experienced|"
               r"erfahren|\bexpert|\bwirtschaftspruefer(?:in)?\b|\bsteuerberater(?:in)?\b|"
               r"\brevisor(?:in)?\b"),
    ("Berufseinstieg", r"\bassociates?\b|\bconsultants?\b|\banalysts?\b|\bassistants?\b|assistent|"
                       r"\bberater(?:in)?\b"),
]

# Anwalts-Berufe (siehe einstellungen.toml) schließen Stellen in diesen Bereichen nicht aus:
# Die Arbeitsagentur ordnet z. B. Internal-Audit-Stellen von Beratungen als "Jurist" ein.
BERUF_EGAL_BEI = {"Interne Revision", "Wirtschaftsprüfung"}
_STUFEN_REGELN = [(stufe, re.compile(muster)) for stufe, muster in STUFEN_REGELN]
_OPTIONAL_SENIOR = re.compile(r"\(\s*(?:senior|sr|snr)\.?\s*-?\s*\)")
_OPTIONAL_JUNIOR = re.compile(r"\(\s*(?:junior|jr)\.?\s*-?\s*\)")
_JUNIOR_SENIOR = re.compile(r"\b(?:junior|jr)\.?\s*/\s*(?:senior|sr|snr)\b\.?|"
                            r"\b(?:senior|sr|snr)\.?\s*/\s*(?:junior|jr)\b\.?")
_TITELTEILE = re.compile(r"\s*[/|,;]\s*|\s+[-–—]\s+|\s+(?:oder|bzw\.?|or)\s+")

# Stufen-Angaben der Bewerbersysteme ("experienced", "Senior Associate", "Berufseinstieg" …).
# Sie zählen nur, wenn der Titel selbst keine Stufe erkennen lässt.
_SYSTEM_STUFEN = [
    ("Berufseinstieg", re.compile(r"\bintern\b|internship|praktik|student|studierend|schueler|trainee|"
                                  r"apprentice|ausbildung|entry|einstieg|einsteig|absolvent|graduate|"
                                  r"junior|young professional")),
    ("Manager", re.compile(r"(?:associate|assistant) director|manager")),
    ("Director & Partner", re.compile(r"director|partner|executive|principal|\bhead\b")),
    ("Senior", re.compile(r"senior|specialist|experienced|berufserfahren|professional|expert")),
    ("Berufseinstieg", re.compile(r"associate|analyst|consultant")),
]


def stufe_aus_system(text) -> str | None:
    t = normalisiere(str(text or ""))
    return next((stufe for stufe, muster in _SYSTEM_STUFEN if t and muster.search(t)), None)


# Bei Firmen mit Standard-Bereich: Stellen dieser Art zählen trotzdem nicht
FACHFREMD = re.compile(
    r"office manag|office assist|back ?office|assistenz|executive assistant|personal assistant|"
    r"team assistant|assistant to|assistent(?:in)? der|empfang|rezeption|marketing|kommunikation|"
    r"communication|recruit|talent|human resources|\bhr\b|people|personal|\bit\b|informatik|"
    r"software|developer|entwickler|engineer|\bdata\b|buchhalt|accountant|controll|steuer|\btax\b|"
    r"lohn|sachbearbeit|kaufm|kauffrau|ausbildung|azubi|auszubild|legal|jurist|recht|sekretaer|"
    r"\bevent|design|sales|vertrieb|facility|hausmeister|fahrer|administrat|investor relations|"
    r"fund admin")

REMOTE_WOERTER = re.compile(
    r"\b(?:remote|homeoffice|home office|mobiles arbeiten|mobile office|deutschlandweit|"
    r"bundesweit|germany|deutschland|deu|de|allemagne|flexibel|flexible|hybrid|und|and)\b")

# Geschlechtsangaben wie (m/w/d) werden aus dem Titel entfernt.
GENDER_MUSTER = re.compile(
    r"\(\s*(?:[mwfdxi]\s*[/|,]?\s*){2,4}\)"
    r"|\(\s*(?:all genders|alle geschlechter|gn\*?|m/w/d|w/m/d|m/w/div\.?|mensch)\s*\)"
    r"|\b(?:m|w|d)\s*/\s*(?:m|w|d)\s*/\s*(?:m|w|d|x)\b",
    re.IGNORECASE,
)


# --- Hilfsfunktionen ---------------------------------------------------------


def umlaute(text: str) -> str:
    t = re.sub(r"[​‌‍⁠﻿­]", "", (text or "").lower())  # unsichtbare Zeichen
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
    t = re.sub(r"\s+([,;:])", r"\1", t)  # "Senior Consultant Audit , Frankfurt" → "…Audit, Frankfurt"
    t = re.sub(r",(?=[A-Za-zÄÖÜäöü])", ", ", t)  # "Frankfurt,Nürnberg" → "Frankfurt, Nürnberg"
    return schreibweise(re.sub(r"[\s\-–—|,:/]+$", "", t).strip())


# Abkürzungen, die in GROSSBUCHSTABEN bleiben
AKRONYME = {"M&A", "IT", "HR", "PE", "VP", "CFO", "CEO", "COO", "CRO", "KPI", "ERP", "SAP", "ESG", "IFRS", "HGB",
            "US", "UK", "EU", "AG", "SE", "GMBH", "KPMG", "PWC", "EY", "BDO", "FDD", "TS", "IKS", "IPO", "DCM", "ECM",
            "PMI", "PMO", "AI", "KI", "CSRD", "BI", "FS", "DACH", "CF", "MBA", "CPA", "WP", "STB"}
_KLEINE_WOERTER = {"and", "or", "of", "the", "as", "a", "an", "in", "im", "for", "to", "und", "oder", "der", "die",
                   "das", "den", "für", "fuer", "mit", "bei", "am", "zum", "zur", "von", "ab"}


def schreibweise(titel: str) -> str:
    """"ANALYST – CORPORATE FINANCE" → "Analyst – Corporate Finance". Abkürzungen bleiben."""
    buchstaben = [z for z in titel if z.isalpha()]
    gross = sum(z.isupper() for z in buchstaben)
    if not buchstaben or gross < 0.6 * len(buchstaben):
        # Gemischte Schreibweise: nur lange Wörter in Großbuchstaben ändern ("SENIOR MANAGER – Turnaround")
        return re.sub(r"\b[A-ZÄÖÜ]{5,}\b", lambda m: m.group(0) if m.group(0) in AKRONYME else m.group(0).capitalize(), titel)

    def wort(m):
        w = m.group(0)
        if w.upper() in AKRONYME:
            return w.upper()
        if w.lower() in _KLEINE_WOERTER and m.start() > 0:
            return w.lower()
        return w.capitalize()
    return re.sub(r"[A-Za-zÄÖÜäöüß&]+", wort, titel)


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
    try:  # RSS: "Thu, 15 Oct 2026 11:46:23 Z"
        return email.utils.parsedate_to_datetime(text).date()
    except (TypeError, ValueError, IndexError):
        return None


def datum_aus_relativ(text: str, heute: date) -> date | None:
    """Workday: "Posted 3 Days Ago", "Vor 26 Tagen ausgeschrieben", "Gestern" …"""
    t = (text or "").lower()
    if "heute" in t or "today" in t:
        return heute
    if "gestern" in t or "yesterday" in t:
        return heute - timedelta(days=1)
    treffer = re.search(r"(\d+)\+?\s*(?:tag|day)", t)
    if treffer:
        return heute - timedelta(days=int(treffer[1]))
    return None


_MONATE = {"jan": 1, "feb": 2, "mar": 3, "mär": 3, "apr": 4, "may": 5, "mai": 5, "jun": 6, "jul": 7,
           "aug": 8, "sep": 9, "oct": 10, "okt": 10, "nov": 11, "dec": 12, "dez": 12}


def datum_text(text: str) -> date | None:
    """"Oct 9, 2026" oder "9. Okt. 2026" (Monatsnamen auf Englisch oder Deutsch)."""
    t = (text or "").strip().lower()
    treffer = (re.search(r"([a-zä]{3})[a-zä]*\.?\s+(\d{1,2}),?\s+(\d{4})", t)
               or re.search(r"(\d{1,2})\.?\s+([a-zä]{3})[a-zä]*\.?\s+(\d{4})", t))
    if not treffer:
        return als_datum(text)
    teile = treffer.groups()
    monat, tag = (teile[0], teile[1]) if teile[0].isalpha() else (teile[1], teile[0])
    try:
        return date(int(teile[2]), _MONATE[monat[:3]], int(tag))
    except (KeyError, ValueError):
        return None


def ohne_tags(text: str) -> str:
    """HTML-Schnipsel als einfacher Text."""
    return re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", text or "")).replace("\xa0", " ")).strip()


def als_zahl(wert, ersatz: int = 0) -> int:
    try:
        return int(str(wert).strip())
    except (TypeError, ValueError):
        return ersatz


def kurz_id(text: str, praefix: str = "ba-") -> str:
    return praefix + hashlib.sha1(text.encode("utf-8")).hexdigest()[:12]


def abrufen(url: str, methode: str = "GET", daten=None, kopf: dict | None = None,
            art: str = "json", versuche: int = 3):
    """Lädt eine Adresse; wiederholt bei vorübergehenden Fehlern."""
    header = {**WEB_HEADER, "Accept-Encoding": "gzip", **(kopf or {})}  # gepackt: weniger Last für die Seiten
    rumpf = None
    if daten is not None:
        rumpf = json.dumps(daten).encode("utf-8")
        header.setdefault("Content-Type", "application/json")
    if art == "json":
        header.setdefault("Accept", "application/json")
    anfrage = urllib.request.Request(url, data=rumpf, headers=header, method=methode)
    for versuch in range(1, versuche + 1):
        try:
            with urllib.request.urlopen(anfrage, timeout=30) as antwort:
                inhalt = antwort.read()
                kodierung = (getattr(antwort, "headers", None) or {}).get("Content-Encoding", "")
            if kodierung.lower() == "gzip" or inhalt[:2] == b"\x1f\x8b":
                inhalt = gzip.decompress(inhalt)
            text = inhalt.decode("utf-8", errors="replace")
            return json.loads(text) if art == "json" else text
        except urllib.error.HTTPError as fehler:
            if fehler.code not in (429, 500, 502, 503, 504) or versuch == versuche:
                raise
        except (urllib.error.URLError, TimeoutError, ConnectionError, json.JSONDecodeError):
            if versuch == versuche:
                raise
        time.sleep(2 * versuch)


# --- Einstellungen und alte Daten ----------------------------------------------


def lade_einstellungen() -> dict:
    with EINSTELLUNGEN.open("rb") as f:
        roh = tomllib.load(f)

    allgemein = roh.get("allgemein", {})
    regionen = []
    for r in roh.get("region", []):
        orte = [str(o) for o in r.get("orte", [])] or [str(r["ort"])]
        regionen.append({
            "name": str(r["name"]),
            "ort": str(r["ort"]),
            "umkreis": int(r.get("umkreis_km", 25)),
            "orte_norm": [normalisiere(o) for o in orte if normalisiere(o)],
        })
    begriffe = [str(b) for b in roh.get("suche", {}).get("begriffe", []) if str(b).strip()]

    # Je Bereich die Stichwörter normalisieren, längste zuerst prüfen.
    bereiche = []
    for name, woerter in roh.get("bereiche", {}).items():
        norm = sorted({normalisiere(w) for w in woerter if normalisiere(w)}, key=len, reverse=True)
        bereiche.append((name, norm))

    ausschluss_roh = roh.get("ausschluss", {})
    ausschluss = [normalisiere(w) for w in ausschluss_roh.get("woerter", [])]
    berufe = [normalisiere(w) for w in ausschluss_roh.get("berufe", [])]
    ausnahmen = sorted({normalisiere(w) for w in ausschluss_roh.get("ausnahmen", []) if normalisiere(w)},
                       key=len, reverse=True)
    firmen_cfg = roh.get("firmen", {})

    if not regionen or not begriffe or not bereiche:
        sys.exit("einstellungen.toml braucht mindestens eine Region, einen Suchbegriff und einen Bereich.")

    firmen = []
    if FIRMENLISTE.exists():
        with FIRMENLISTE.open("rb") as f:
            firmen = [x for x in tomllib.load(f).get("firma", []) if x.get("name") and x.get("system")]

    return {
        "max_alter": max(1, min(100, int(allgemein.get("max_alter_tage", 60)))),
        "ohne_pav": bool(allgemein.get("ohne_personalvermittlung", True)),
        "ohne_zeitarbeit": bool(allgemein.get("ohne_zeitarbeit", True)),
        "regionen": regionen,
        "begriffe": begriffe,
        "bereiche": bereiche,
        "ausschluss": [w for w in ausschluss if w],
        "ausschluss_berufe": [w for w in berufe if w],
        "ausnahmen": ausnahmen,
        "ort_woerter": sorted({o for r in regionen for o in r["orte_norm"]}, key=len, reverse=True),
        "remote": bool(firmen_cfg.get("remote_einbeziehen", True)),
        "remote_region": str(firmen_cfg.get("remote_region", "Bundesweit / Remote")),
        "firmen": firmen,
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
            muster = f" {wort} " if len(wort) <= 3 else wort  # kurze Wörter ("IKS", "FDD") nur als ganzes Wort
            if muster in rest:
                gefunden = True
                rest = rest.replace(muster, " ")
        if gefunden:
            treffer.append(name)
    return treffer


def arten_aus_text(text: str) -> set[str]:
    """Anstellungsart aus Angaben der Bewerbersysteme ("Vollzeit / Teilzeit", "internship" …)."""
    t = normalisiere(text)
    arten = set()
    if re.search(r"vollzeit|full ?time|\bfull\b", t):
        arten.add("Vollzeit")
    if re.search(r"teilzeit|part ?time|\bpart\b", t):
        arten.add("Teilzeit")
    if re.search(r"praktik|\bintern\b|internship", t):
        arten.add("Praktikum")
    if re.search(r"werkstud|working student|studentjob", t):
        arten.add("Werkstudent")
    if re.search(r"trainee", t):
        arten.add("Trainee")
    return arten


# "Vollzeit oder Teilzeit", "Teil- oder Vollzeit", "Voll/Teilzeit", "part/full-time" im Titel
_TEILZEIT_IM_TITEL = re.compile(r"teilzeit|\bteil (?:oder |und |bzw )?vollzeit|\bpart (?:or |and )?(?:full )?time\b")
_VOLLZEIT_IM_TITEL = re.compile(r"vollzeit|\bvoll (?:oder |und |bzw )?teilzeit|\bfull time\b")


def bestimme_arten(arten: set[str], titel_norm: str) -> list[str]:
    def hat(art: str) -> bool:
        return bool(ART_MUSTER[art].search(titel_norm))

    # Der Titel hat Vorrang vor den Angaben der Bewerbersysteme ("Praktikant/Werkstudent" = beides)
    aus_titel = [a for a in ("Werkstudent", "Praktikum", "Abschlussarbeit") if hat(a)]
    if aus_titel:
        return aus_titel
    if "Werkstudent" in arten:
        return ["Werkstudent"]
    ergebnis = set(arten)
    if _TEILZEIT_IM_TITEL.search(titel_norm):
        ergebnis.add("Teilzeit")
    if _VOLLZEIT_IM_TITEL.search(titel_norm):
        ergebnis.add("Vollzeit")
    if hat("Trainee"):
        ergebnis.discard("Praktikum")
        ergebnis.add("Trainee")
    reihenfolge = ["Vollzeit", "Teilzeit", "Trainee", "Praktikum"]
    return [a for a in reihenfolge if a in ergebnis] or ["Vollzeit"]


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


def ordne_regionen(orte: list[str], cfg: dict) -> tuple[list[str], str, list[str]]:
    """Welche Regionen passen zu den Orten? Liefert (Regionen, angezeigter Ort, weitere Orte)."""
    regionen, passende, andere = set(), [], []
    for ort in orte:
        text = f" {normalisiere(ort)} "
        if " frankfurt " in text and " oder " in text:  # Frankfurt (Oder)
            andere.append(ort)
            continue
        funde = [(r["name"], o) for r in cfg["regionen"] for o in r["orte_norm"] if f" {o} " in text]
        # Der längere Ortsname gewinnt: "Mörfelden-Walldorf" ist nicht Walldorf (Baden)
        treffer = {name for name, o in funde if not any(o != o2 and f" {o} " in f" {o2} " for _, o2 in funde)}
        if treffer:
            regionen |= treffer
            passende.append(ort)
        elif cfg["remote"] and not REMOTE_WOERTER.sub(" ", text).strip() and text.strip():
            regionen.add(cfg["remote_region"])
            passende.append(ort)
        else:
            andere.append(ort)
    reihenfolge = [r["name"] for r in cfg["regionen"]] + [cfg["remote_region"]]
    sichtbar = []
    for ort in passende + andere:
        ort = ort_anzeige(ort)
        if ort and ort not in sichtbar:
            sichtbar.append(ort)
    return [r for r in reihenfolge if r in regionen], (sichtbar or [""])[0], sichtbar[1:21]


_BUNDESLAENDER = (r"hesse|hessen|bavaria|bayern|baden[- ]w(?:ü|u|ue)rttemberg|north rhine[- ]westphalia|"
                  r"nordrhein[- ]westfalen|rhineland[- ]palatinate|rheinland[- ]pfalz|lower saxony|niedersachsen|"
                  r"saxony|sachsen|thuringia|thüringen|saarland|schleswig[- ]holstein|brandenburg|"
                  r"mecklenburg[- ]vorpommern|saxony[- ]anhalt|sachsen[- ]anhalt")


# "Frankfurt", "Frankfurt a. M.", "Frankfurt/Main" … – aber nicht Frankfurt (Oder)
_FRANKFURT_AM_MAIN = re.compile(r"frankfurt(?:\s*(?:am\s+main|a\.?\s*m(?:ain)?\.?|/\s*m(?:ain)?\.?|\(\s*main\s*\)))?", re.I)


def ort_anzeige(ort: str) -> str:
    """"Frankfurt, Hesse, Germany" / "Germany - Frankfurt" → nur der Ort (für die Anzeige)."""
    kurz = re.sub(r"[\s,]+(?:germany|deutschland|deu|de|allemagne)\s*$", "", ort.strip(), flags=re.I)
    kurz = re.sub(r"^\s*(?:germany|deutschland|deu)\s*[-–,:]\s*", "", kurz, flags=re.I).strip(" ,")
    kurz = re.sub(rf",\s*(?:{_BUNDESLAENDER})\s*$", "", kurz, flags=re.I).strip(" ,")
    if re.fullmatch(r"germany|deutschland|deu", kurz, flags=re.I):
        return "Deutschland"
    if _FRANKFURT_AM_MAIN.fullmatch(kurz):
        return "Frankfurt am Main"
    return _DEUTSCHE_NAMEN.get(kurz.lower(), kurz) or ort.strip()


# Englische Städtenamen deutscher Standorte (Greenhouse, Workday …)
_DEUTSCHE_NAMEN = {"munich": "München", "cologne": "Köln", "dusseldorf": "Düsseldorf", "duesseldorf": "Düsseldorf",
                   "nuremberg": "Nürnberg", "hanover": "Hannover", "brunswick": "Braunschweig"}


def ist_ausgeschlossen(text_norm: str, cfg: dict) -> bool:
    """Ausschlussliste prüfen; Ausnahmen wie "Prüfungsassistenz" zählen nicht als "Assistenz"."""
    for ausnahme in cfg["ausnahmen"]:
        text_norm = text_norm.replace(ausnahme, " ")
    return any(w in text_norm for w in cfg["ausschluss"])


def titel_schluessel(titel: str, cfg: dict) -> str:
    """Titel ohne Ortsnamen ("Senior Consultant Audit, Frankfurt") – zum Erkennen von Dubletten."""
    t = f" {normalisiere(titel)} "
    for wort in cfg["ort_woerter"]:
        t = t.replace(f" {wort} ", " ")
    return " ".join(w for w in t.split() if w not in _FUELLWOERTER)


_FUELLWOERTER = {"am", "main", "a", "m", "in", "im", "standort", "standorte", "bundesweit", "remote", "hybrid",
                 "germany", "deutschland", "oder", "und", "or", "and", "fuer", "for"}


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
    for schluessel in ("stellenangebote", "ergebnisliste", "ergebnisse", "stellen", "jobs", "content"):
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
    bekannte = {"stellenangebote", "ergebnisliste", "maxErgebnisse", "facetten", "page", "size", "ergebnisse"}
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
    beruf_norm = normalisiere(stelle["beruf"])

    # Die Ausschlussliste gilt für den Titel. Den von der BA zugeordneten Beruf
    # prüfen wir nur gegen die Berufe-Liste (z. B. Rechtsanwalt) – die Zuordnung
    # der BA ist sonst oft ungenau (z. B. "Internal Auditor" als Qualitäts-Auditor).
    if ist_ausgeschlossen(titel_norm, cfg):
        beispiele["ausgeschlossen"][stelle["titel"]] += 1
        return

    bereiche = finde_bereiche(titel_norm, cfg["bereiche"])
    if (any(w in beruf_norm for w in cfg["ausschluss_berufe"])
            and not set(bereiche) & BERUF_EGAL_BEI):  # Prüfung/Revision ist keine Anwaltsstelle
        beispiele["ausgeschlossen"][f"{stelle['titel']} [Beruf: {stelle['beruf']}]"] += 1
        return
    if not bereiche and stelle["beruf"]:
        if any(w in beruf_norm for w in cfg["ausschluss"]):
            beispiele["ausgeschlossen"][f"{stelle['titel']} [Beruf: {stelle['beruf']}]"] += 1
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


def signatur(titel: str, firma: str, ort: str) -> str:
    return "|".join(normalisiere(x) for x in (titel, firma, ort))


def baue_ba_stellen(treffer, cfg, heute) -> dict[str, dict]:
    """Rohtreffer der BA zu Stellen zusammenfassen (gleicher Titel, Firma, Ort = eine Stelle)."""
    region_reihenfolge = [r["name"] for r in cfg["regionen"]]
    gruppen: dict[str, list[dict]] = {}
    for e in treffer.values():
        gruppen.setdefault(signatur(e["titel"], e["firma"], e["orte"][0] if e["orte"] else ""), []).append(e)

    stellen = {}
    for gruppe in gruppen.values():
        ids = sorted(kurz_id(e["refnr"]) for e in gruppe)
        neueste = max(gruppe, key=lambda e: e["datum"] or date.min)
        aelteste = min((e["datum"] for e in gruppe if e["datum"]), default=None)
        regionen = set().union(*(e["regionen"] for e in gruppe))
        abfrage_arten = set().union(*(e["abfrage_arten"] for e in gruppe))
        orte = []
        for e in gruppe:
            orte += [o for o in e["orte"] if o not in orte]
        arten = bestimme_arten(abfrage_arten, normalisiere(neueste["titel"]))

        stelle = {
            "ids": ids,  # wird beim Zusammenführen durch die endgültige ID ersetzt
            "titel": neueste["titel"],
            "firma": neueste["firma"],
            "ort": orte[0] if orte else "",
            "plz": neueste["plz"],
            "regionen": [r for r in region_reihenfolge if r in regionen],
            "bereiche": neueste["bereiche"],
            "arten": arten,
            "stufen": bestimme_stufen(neueste["titel"], arten),
            "veroeffentlicht": (aelteste or heute).isoformat(),
            "link": BA_DETAILSEITE.format(refnr=urllib.parse.quote(neueste["refnr"])),
            "quelle": QUELLE_BA,
            "quellen": [QUELLE_BA],
            "herkunft": "ba",
            # Übergang von Version 1.0: alte ID aus Titel und Firma ohne Ort
            "_v1_id": kurz_id(f"{normalisiere(neueste['titel'])}|{normalisiere(neueste['firma'])}|"),
        }
        if len(orte) > 1:
            stelle["weitere_orte"] = orte[1:6]
        extern = neueste["extern"] or next((e["extern"] for e in gruppe if e["extern"]), None)
        if extern:
            stelle["extern"] = extern
        stellen[ids[0]] = stelle
    return stellen


# --- Firmen-Karriereseiten -------------------------------------------------------


def text_von(element, pfad: str) -> str:
    gefunden = element.find(pfad)
    return (gefunden.text or "").strip() if gefunden is not None and gefunden.text else ""


def quelle_personio(firma: dict, heute: date) -> list[dict]:
    konto = firma["konto"]
    basis = f"https://{konto}.jobs.personio.{firma.get('domain', 'de')}"
    xml = abrufen(f"{basis}/xml?language=de", art="text")
    wurzel = ET.fromstring(xml.encode("utf-8"))
    ergebnis = []
    for pos in wurzel.iter("position"):
        nummer = text_von(pos, "id")
        titel = text_von(pos, "name")
        if not nummer or not titel:
            continue
        orte = [text_von(pos, "office")] + [o.text.strip() for o in pos.findall("additionalOffices/office") if o.text]
        # employmentType: permanent, intern, trainee, working_student …; schedule: full-time, part-time …
        arten = arten_aus_text(f"{text_von(pos, 'employmentType')} {text_von(pos, 'schedule')}")
        ergebnis.append({
            "id": nummer,
            "titel": titel,
            "firma": text_von(pos, "subcompany") or firma["name"],
            "orte": [o for o in orte if o],
            "datum": als_datum(text_von(pos, "createdAt")),
            "link": f"{basis}/job/{nummer}?language=de",
            "hinweise": [text_von(pos, "department"), text_von(pos, "recruitingCategory")],
            "arten": arten,
            "stufe": stufe_aus_system(text_von(pos, "seniority")),
        })
    return ergebnis


def quelle_recruitee(firma: dict, heute: date) -> list[dict]:
    antwort = abrufen(f"https://{firma['konto']}.recruitee.com/api/offers/")
    ergebnis = []
    for o in antwort.get("offers", []):
        orte = [l.get("city") for l in o.get("locations") or [] if l.get("city")] or [o.get("city") or o.get("location") or ""]
        ergebnis.append({
            "id": str(o.get("id")),
            "titel": o.get("title") or "",
            "firma": firma["name"],
            "orte": [x for x in orte if x],
            "datum": als_datum(o.get("published_at") or o.get("created_at")),
            "link": o.get("careers_url") or o.get("url") or "",
            "hinweise": [o.get("department") or ""],
            "arten": arten_aus_text(o.get("employment_type_code") or ""),
            "stufe": None,
        })
    return ergebnis


def quelle_greenhouse(firma: dict, heute: date) -> list[dict]:
    host = "boards-api.eu.greenhouse.io" if firma.get("eu") else "boards-api.greenhouse.io"
    antwort = abrufen(f"https://{host}/v1/boards/{firma['konto']}/jobs")
    return [{
        "id": str(j.get("id")),
        "titel": j.get("title") or "",
        "firma": firma["name"],
        "orte": [(j.get("location") or {}).get("name") or ""],
        "datum": als_datum(j.get("first_published") or j.get("updated_at")),
        "link": j.get("absolute_url") or "",
        "hinweise": [],
        "arten": set(),
        "stufe": None,
    } for j in antwort.get("jobs", [])]


def quelle_workday(firma: dict, heute: date) -> list[dict]:
    host, mandant = firma["host"], firma["mandant"]
    gefunden: dict[str, dict] = {}
    for seite in firma.get("seiten") or [firma.get("seite", "External")]:
        for suchtext in firma.get("suche") or [""]:
            offset, gesamt = 0, None
            while offset < 400:
                antwort = abrufen(f"https://{host}/wday/cxs/{mandant}/{seite}/jobs", methode="POST",
                                  daten={"appliedFacets": {}, "limit": 20, "offset": offset, "searchText": suchtext})
                posten = antwort.get("jobPostings") or []
                if gesamt is None:
                    gesamt = als_zahl(antwort.get("total"), 0)
                for p in posten:
                    pfad = p.get("externalPath") or ""
                    ort = p.get("locationsText") or ""
                    if not ort or re.match(r"^\d+\s", ort):  # "2 Locations" – Ort aus der Adresse lesen
                        teile = pfad.split("/")
                        ort = teile[2].replace("-", " ") if len(teile) > 2 else ""
                    gefunden[pfad] = {
                        "id": pfad,
                        "titel": p.get("title") or "",
                        "firma": firma["name"],
                        "orte": [ort] if ort else [],
                        "datum": datum_aus_relativ(p.get("postedOn") or "", heute),
                        "link": f"https://{host}/{seite}{pfad}",
                        "hinweise": [],
                        "arten": set(),
                        "stufe": None,
                    }
                offset += 20
                time.sleep(PAUSE_SEKUNDEN)
                if len(posten) < 20 or (gesamt and offset >= gesamt):
                    break
    return list(gefunden.values())


def quelle_phenom(firma: dict, heute: date) -> list[dict]:
    """Stellensuche von Phenom (PwC). Die Reihenfolge der Treffer wechselt von Abruf zu
    Abruf; beim Blättern fehlen deshalb manche Stellen, andere kommen doppelt. Darum
    blättern wir bis zu fünfmal durch, bis so viele Stellen da sind, wie die Seite meldet."""
    gefunden: dict[str, dict] = {}
    gesamt = 0
    for durchgang in range(5):
        try:
            gesamt = _phenom_durchgang(firma, gefunden)
        except Exception:  # noqa: BLE001
            if durchgang == 0:
                raise
            break  # mit den Stellen aus den bisherigen Durchgängen weiterarbeiten
        if not gesamt or len(gefunden) >= gesamt:
            break
    GESAMT_LAUT_QUELLE[herkunft_von(firma)] = gesamt
    return list(gefunden.values())


def _phenom_durchgang(firma: dict, gefunden: dict[str, dict]) -> int:
    """Einmal durch alle Seiten blättern; neue Stellen landen in `gefunden`. Liefert die Gesamtzahl."""
    basis = firma["basis"].rstrip("/")
    kopf = {"Origin": basis, "Referer": f"{basis}/de/de/search-results"}
    start, gesamt = 0, 0
    for seite in range(60):  # höchstens 60 Seiten
        anfrage = {
            "lang": firma.get("sprache", "de_de"), "deviceType": "desktop", "country": firma.get("land", "de"),
            "pageName": "search-results", "ddoKey": "refineSearch", "sortBy": "", "subsearch": "",
            "from": start, "jobs": True, "counts": False, "all_fields": ["category", "city", "grade", "type"],
            "size": 100, "clearAll": False, "jdsource": "facets", "isSliderEnable": False,
            "keywords": "", "global": True, "selected_fields": {}, "locationData": {},
        }
        antwort = abrufen(f"{basis}/widgets", methode="POST", daten=anfrage, kopf=kopf)
        suche = antwort.get("refineSearch") or {}
        stellen = (suche.get("data") or {}).get("jobs") or []
        if seite == 0:
            gesamt = als_zahl(suche.get("totalHits"), 0)
        for j in stellen:
            orte = [re.sub(r",\s*[A-Z]{3}$", "", o).strip() for o in j.get("multi_location") or []] or [j.get("city") or ""]
            nummer = str(j.get("reqId") or j.get("jobId") or j.get("jobSeqNo") or "")
            kennung = str(j.get("jobSeqNo") or nummer)
            if kennung in gefunden:
                continue
            gefunden[kennung] = {
                "id": kennung,
                "titel": j.get("title") or "",
                "firma": firma["name"],
                "orte": [o for o in orte if o],
                "datum": als_datum(j.get("postedDate") or j.get("dateCreated")),
                "link": j.get("jobUrl") or f"{basis}{firma.get('jobpfad', '/job/')}{nummer}",
                # Die Kategorie (Assurance, Deals, Tax …) ist zu grob, um den Bereich daraus abzulesen
                "hinweise": [],
                "arten": arten_aus_text(j.get("type") or ""),
                "stufe": stufe_aus_system(j.get("grade")),
            }
        start += len(stellen)  # falls der Server weniger als 100 je Seite liefert
        time.sleep(PAUSE_SEKUNDEN)
        if not stellen or (gesamt and start >= gesamt):
            break
    return gesamt


def quelle_rss(firma: dict, heute: date) -> list[dict]:
    ergebnis = []
    for feed in firma.get("feeds", []):
        url, ort = (feed.get("url"), feed.get("ort", "")) if isinstance(feed, dict) else (feed, "")
        wurzel = ET.fromstring(abrufen(url, art="text").encode("utf-8"))
        for item in wurzel.iter("item"):
            titel = re.sub(r"^\s*\d{4}-\d+\s*-\s*", "", text_von(item, "title"))  # "2025-788 - …"
            link = text_von(item, "link")
            kategorie = " ".join((c.text or "") for c in item.findall("category"))
            ergebnis.append({
                "id": link or titel,
                "titel": titel,
                "firma": firma["name"],
                "orte": [ort] if ort else [],
                "datum": als_datum(text_von(item, "pubDate")),
                "link": link,
                "hinweise": [kategorie],
                "arten": arten_aus_text(kategorie),
                "stufe": None,
            })
    return ergebnis


def quelle_nextjs(firma: dict, heute: date) -> list[dict]:
    html = abrufen(firma["url"], art="text")
    treffer = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', html, re.S)
    if not treffer:
        raise ValueError("Keine eingebetteten Seitendaten (__NEXT_DATA__) gefunden")
    daten = json.loads(treffer.group(1))
    stellen = ((daten.get("props") or {}).get("pageProps") or {}).get("jobs") or []
    basis = re.match(r"https?://[^/]+", firma["url"]).group(0)
    ergebnis = []
    for j in stellen:
        orte = j.get("displayedCities") or [suche_tief(c, ("name", "title", "city")) for c in j.get("cities") or []]
        if isinstance(orte, str):  # "Berlin; Frankfurt am Main"
            orte = [orte]
        if not orte and j.get("city"):
            orte = [suche_tief(j["city"], ("name", "title", "city")) or str(j["city"])]
        stufen = [stufe_aus_system(suche_tief(x, ("name", "title", "label")) if isinstance(x, dict) else x)
                  for x in j.get("careerLevels") or []]
        link = j.get("applyUrl") or (f"{basis}/job/{j['jobId']}" if j.get("jobId") else firma["url"])
        ergebnis.append({
            "id": link,
            "titel": j.get("title") or "",
            "firma": firma["name"],
            "orte": [str(o) for o in orte if o],
            "datum": als_datum(j.get("publishedAt") or j.get("jobCreatedAt") or j.get("createdAt")),
            "link": link,
            "hinweise": [str(j.get("department") or "")],
            "arten": arten_aus_text(j.get("positionType") or ""),
            "stufe": next((s for s in stufen if s), None),
        })
    return ergebnis


def datum_sf(text: str) -> date | None:
    """SuccessFactors-Feed: "Thu, 24 08 2023 00:00:00 GMT" (Monat als Zahl)."""
    treffer = re.search(r"(\d{1,2}) (\d{1,2}) (\d{4})", text or "")
    if treffer:
        try:
            return date(int(treffer[3]), int(treffer[2]), int(treffer[1]))
        except ValueError:
            return None
    return als_datum(text)


def quelle_successfactors(firma: dict, heute: date) -> list[dict]:
    """Stellen-Feed für Jobbörsen von SAP SuccessFactors (z. B. jobs.kpmg.de/feed/…).
    Enthält alle Standorte einer Stelle (multicity), Fachbereich (shift) und Zielgruppe."""
    wurzel = ET.fromstring(abrufen(firma["feed"], art="text").encode("utf-8"))
    ohne_marken = {m.lower() for m in firma.get("ohne_marken", [])}
    ergebnis = []
    for job in wurzel.iter("job"):
        if text_von(job, "brand").lower() in ohne_marken:  # z. B. die Anwaltsgesellschaft "kpmgLAW"
            continue
        link = text_von(job, "url")
        orte = [o.strip() for o in text_von(job, "multicity").split(";") if o.strip()] or [text_von(job, "city")]
        ergebnis.append({
            "id": text_von(job, "AltID") or text_von(job, "ID") or link,
            "titel": text_von(job, "title"),
            "firma": firma["name"],
            "orte": [o for o in orte if o],
            "datum": datum_sf(text_von(job, "created")) or als_datum(text_von(job, "posteddate")),
            "link": re.sub(r"\?feedId=\d+$", "", link),
            "hinweise": [text_von(job, "shift")],
            "arten": arten_aus_text(text_von(job, "shifttype")),
            "stufe": stufe_aus_system(text_von(job, "department") or text_von(job, "customfield2")),
        })
    return ergebnis


def quelle_oracle(firma: dict, heute: date) -> list[dict]:
    """Oracle Recruiting Cloud (z. B. Kroll): öffentliche Schnittstelle der Bewerberseite."""
    host, seite = firma["host"], firma.get("seite", "CX_1")
    basis = f"https://{host}/hcmRestApi/resources/latest/recruitingCEJobRequisitions"
    ergebnis, offset = [], 0
    for _ in range(20):  # höchstens 4000 Stellen
        antwort = abrufen(f"{basis}?onlyData=true&expand=requisitionList.secondaryLocations&finder=findReqs;"
                          f"siteNumber={seite},limit=200,offset={offset},sortBy=POSTING_DATES_DESC")
        block = (antwort.get("items") or [{}])[0]
        liste = block.get("requisitionList") or []
        for r in liste:
            orte = [r.get("PrimaryLocation") or ""] + [s.get("Name") or "" for s in r.get("secondaryLocations") or []]
            ergebnis.append({
                "id": str(r.get("Id")),
                "titel": r.get("Title") or "",
                "firma": firma["name"],
                "orte": [o for o in orte if o],
                "datum": als_datum(r.get("PostedDate")),
                "link": f"https://{host}/hcmUI/CandidateExperience/de/sites/{seite}/job/{r.get('Id')}",
                "hinweise": [r.get("JobFamily") or "", r.get("JobFunction") or ""],
                "arten": arten_aus_text(f"{r.get('JobSchedule') or ''} {r.get('JobType') or ''}"),
                "stufe": stufe_aus_system(r.get("ManagerLevel") or ""),
            })
        offset += len(liste)
        time.sleep(PAUSE_SEKUNDEN)
        if not liste or offset >= als_zahl(block.get("TotalJobsCount"), 0):
            break
    return ergebnis


def quelle_talemetry(firma: dict, heute: date) -> list[dict]:
    """Stellensuche als Webseite (Talemetry/Jobvite, z. B. Alvarez & Marsal), 25 Stellen je Seite."""
    basis = firma["basis"].rstrip("/")
    gefunden: dict[str, dict] = {}
    for ort in firma.get("suche") or [""]:
        for nummer in range(1, 21):
            parameter = {"location": ort, **({"page": nummer} if nummer > 1 else {})}
            seite = abrufen(f"{basis}/search/jobs?{urllib.parse.urlencode(parameter)}", art="text")
            bloecke = seite.split('class="jobs-section__item')[1:]
            for block in bloecke:
                a = re.search(r'<a href="([^"]*/jobs/(\d+)[^"]*)"[^>]*>(.*?)</a>', block, re.S)
                if not a:
                    continue
                ort_m = re.search(r"Location:\s*</span>(.*?)</div>", block, re.S)
                datum_m = re.search(r"Date Posted:\s*</span>(.*?)</div>", block, re.S)
                typ_m = re.search(r"JobType:\s*([^<\n]*)", block)
                einheit_m = re.search(r"BusinessUnit:\s*([^<\n]*)", block)
                gefunden[a.group(2)] = {
                    "id": a.group(2),
                    "titel": ohne_tags(a.group(3)),
                    "firma": firma["name"],
                    "orte": [ohne_tags(ort_m.group(1))] if ort_m else [],
                    "datum": datum_text(ohne_tags(datum_m.group(1))) if datum_m else None,
                    "link": html.unescape(a.group(1)),
                    "hinweise": [einheit_m.group(1).strip()] if einheit_m else [],
                    "arten": arten_aus_text(typ_m.group(1)) if typ_m else set(),
                    "stufe": None,
                }
            time.sleep(PAUSE_SEKUNDEN)
            if len(bloecke) < 25:
                break
    return list(gefunden.values())


def quelle_ebnerstolz(firma: dict, heute: date) -> list[dict]:
    """Stellenliste von Ebner Stolz: je Standort und Fachbereich gefiltert (höchstens 20 je Abfrage)."""
    basis = firma.get("basis", "https://www.ebnerstolz.de").rstrip("/")
    seite = abrufen(f"{basis}/de/karriere/stellenangebote/", art="text")
    tag = re.search(r'<[^>]*data-live-name-value="element_vacancy_list"[^>]*>', seite)
    props = tag and re.search(r'data-live-props-value="([^"]*)"', tag.group(0))
    if not props:
        raise ValueError("Stellenliste nicht gefunden – hat sich der Aufbau der Seite geändert?")
    props = html.unescape(props.group(1))
    gefunden: dict[str, dict] = {}
    for code, ortsname in (firma.get("standorte") or {"60325": "Frankfurt am Main"}).items():
        for fach in firma.get("fachbereiche") or [""]:
            auswahl = {"selectedLocations": [code], **({"selectedSubjects": [fach]} if fach else {})}
            abfrage = urllib.parse.urlencode({"props": props, "updated": json.dumps(auswahl)})
            antwort = abrufen(f"{basis}/_components/element_vacancy_list?{abfrage}", art="text",
                              kopf={"Accept": "application/vnd.live-component+html"})
            for gruppe in re.split(r"(?=<li\s[^>]*is_vacancy_group[\s\"])", antwort)[1:]:
                kopf = re.search(r"<h4[^>]*>(.*?)</h4>", gruppe, re.S)
                bereich = ohne_tags(kopf.group(1)) if kopf else ""
                for a in re.finditer(r'<a href="([^"]*-v(\d+)\.html)"[^>]*>(.*?)</a>', gruppe, re.S):
                    span = re.search(r"<span[^>]*>(.*?)</span>", a.group(3), re.S)
                    stelle = gefunden.setdefault(a.group(2), {
                        "id": a.group(2),
                        "titel": ohne_tags(span.group(1) if span else a.group(3)),
                        "firma": firma["name"],
                        "orte": [],
                        "datum": None,
                        "link": urllib.parse.urljoin(basis + "/", html.unescape(a.group(1))),
                        "hinweise": [],
                        "arten": set(),
                        "stufe": None,
                    })
                    if ortsname not in stelle["orte"]:
                        stelle["orte"].append(ortsname)
                    if bereich and bereich not in stelle["hinweise"]:
                        stelle["hinweise"].append(bereich)
            time.sleep(PAUSE_SEKUNDEN)
    return list(gefunden.values())


QUELLEN = {
    "personio": quelle_personio,
    "recruitee": quelle_recruitee,
    "greenhouse": quelle_greenhouse,
    "workday": quelle_workday,
    "phenom": quelle_phenom,
    "rss": quelle_rss,
    "nextjs": quelle_nextjs,
    "successfactors": quelle_successfactors,
    "oracle": quelle_oracle,
    "talemetry": quelle_talemetry,
    "ebnerstolz": quelle_ebnerstolz,
}


# Wie viele Stellen eine Quelle selbst meldet (zum Prüfen, ob alle geladen wurden)
GESAMT_LAUT_QUELLE: dict[str, int] = {}


def herkunft_von(firma: dict) -> str:
    return f"{firma['system']}:{firma.get('konto') or firma.get('mandant') or normalisiere(firma['name']).replace(' ', '-')}"


def baue_firmenstelle(e: dict, firma: dict, cfg: dict, zaehler: Counter, proben: dict) -> dict | None:
    """Wendet Regionen, Ausschlussliste, Bereiche und Stufen auf eine Firmen-Stelle an.
    In `proben` landen Beispiele verworfener Stellen (für die Diagnose)."""
    titel = bereinige_titel(e["titel"])
    titel_norm = normalisiere(titel)
    if not titel or not e.get("link"):
        zaehler["unlesbar"] += 1
        return None

    # Mehrere Orte in einem Feld ("Berlin; Frankfurt am Main") aufteilen
    orte = [t.strip() for o in e.get("orte") or [] for t in re.split(r"\s*[;|\n]\s*", str(o)) if t.strip()]
    orte = orte or ([firma["sitz"]] if firma.get("sitz") else [])
    regionen, ort, weitere = ordne_regionen(orte, cfg)
    if not regionen:
        zaehler["ausserhalb"] += 1
        proben["ausserhalb"].update(orte[:1] or ["(kein Ort)"])
        return None
    if ist_ausgeschlossen(titel_norm, cfg):
        zaehler["ausgeschlossen"] += 1
        proben["ausgeschlossen"].append(titel)
        return None

    # Bereich aus dem Titel; sonst aus Abteilung/Kategorie der Anzeige (aber nicht für
    # Bürojobs, IT, Steuern usw.); sonst der Standard-Bereich der Firma (nur mit Stufe).
    bereiche = finde_bereiche(titel_norm, cfg["bereiche"])
    fachfremd = bool(FACHFREMD.search(titel_norm))
    if not bereiche and not fachfremd:
        for hinweis in e.get("hinweise") or []:
            bereiche = finde_bereiche(normalisiere(hinweis), cfg["bereiche"])
            if bereiche:
                break

    arten = bestimme_arten(e.get("arten") or set(), titel_norm)
    stufen = bestimme_stufen(titel, arten)
    if stufen == [OHNE_STUFE] and e.get("stufe"):
        stufen = [e["stufe"]]

    bekannte = {name for name, _ in cfg["bereiche"]}
    if not bereiche and firma.get("bereiche") and stufen != [OHNE_STUFE] and not fachfremd:
        bereiche = [b for b in firma["bereiche"] if b in bekannte]
    if not bereiche:
        zaehler["kein_bereich"] += 1
        proben["kein_bereich"].append(titel)
        return None

    herkunft = herkunft_von(firma)
    stelle = {
        "id": kurz_id(f"{herkunft}|{e['id']}", "fs-"),
        "titel": titel,
        # Angezeigt wird der Name aus firmen.toml (nicht Unterfirmen wie "60 TWS" bei Nexia)
        "firma": firma["name"],
        "ort": ort,
        "plz": "",
        "regionen": regionen,
        "bereiche": bereiche,
        "arten": arten,
        "stufen": stufen,
        "veroeffentlicht": (e.get("datum") or None) and e["datum"].isoformat(),
        "link": e["link"],
        "quelle": QUELLE_FIRMA,
        "quellen": [QUELLE_FIRMA],
        "herkunft": herkunft,
        # Namensbestandteile zum Erkennen derselben Anzeige bei der Arbeitsagentur
        "_kern": firmenkern(" ".join([firma["name"], e.get("firma") or "", *firma.get("aliase", [])])),
    }
    if weitere:
        stelle["weitere_orte"] = weitere
    zaehler["im_radar"] += 1
    return stelle


def sammle_firmen(cfg: dict, heute: date, protokoll: list) -> tuple[list[dict], list[dict], set[str]]:
    """Fragt alle Firmen ab. Liefert (Stellen, Bericht je Firma, ausgefallene Herkünfte)."""
    stellen, bericht, ausgefallen = [], [], set()
    GESAMT_LAUT_QUELLE.clear()
    for firma in cfg["firmen"]:
        abruf = QUELLEN.get(firma["system"])
        eintrag = {"name": firma["name"], "system": firma["system"], "herkunft": herkunft_von(firma)}
        if not abruf:
            eintrag.update(status="fehler", fehler=f"unbekanntes System '{firma['system']}'")
            bericht.append(eintrag)
            continue
        try:
            roh = abruf(firma, heute)
        except Exception as fehler:  # noqa: BLE001
            ausgefallen.add(herkunft_von(firma))
            eintrag.update(status="fehler", fehler=str(fehler)[:200])
            protokoll.append(f"{firma['name']} ({firma['system']}): {str(fehler)[:160]}")
            bericht.append(eintrag)
            continue
        zaehler = Counter()
        proben = {"ausserhalb": Counter(), "ausgeschlossen": [], "kein_bereich": []}
        gesehen_ids = set()
        for e in roh:
            if e["id"] in gesehen_ids:
                continue
            gesehen_ids.add(e["id"])
            stelle = baue_firmenstelle(e, firma, cfg, zaehler, proben)
            if stelle:
                stellen.append(stelle)
        eintrag.update(status="ok", gefunden=len(gesehen_ids), im_radar=zaehler["im_radar"],
                       ausserhalb=zaehler["ausserhalb"], kein_bereich=zaehler["kein_bereich"],
                       ausgeschlossen=zaehler["ausgeschlossen"],
                       # Beispiele für die Fehlersuche: in deinen Regionen, aber verworfen
                       beispiele_kein_bereich=sorted(set(proben["kein_bereich"]))[:15],
                       beispiele_ausgeschlossen=sorted(set(proben["ausgeschlossen"]))[:10],
                       orte_ausserhalb=[o for o, _ in proben["ausserhalb"].most_common(8)])
        gesamt = GESAMT_LAUT_QUELLE.get(eintrag["herkunft"])
        if gesamt:
            eintrag["gesamt_laut_seite"] = gesamt
            if len(gesehen_ids) < gesamt:
                protokoll.append(f"{firma['name']}: nur {len(gesehen_ids)} von {gesamt} Stellen geladen")
        bericht.append(eintrag)
        time.sleep(PAUSE_SEKUNDEN)
    return stellen, bericht, ausgefallen


# --- Zusammenführen und Speichern ------------------------------------------------


# Allgemeine Namensteile, die beim Vergleich von Firmennamen nicht zählen
_RECHTSFORMEN = {
    "gmbh", "ag", "kg", "kgaa", "co", "mbh", "mbb", "partg", "partnerschaft", "partnerschaftsgesellschaft",
    "wpg", "stbg", "wirtschaftspruefungsgesellschaft", "steuerberatungsgesellschaft", "rechtsanwaltsgesellschaft",
    "wirtschaftspruefer", "steuerberater", "rechtsanwaelte", "llp", "ltd", "inc", "se", "und", "the",
    "deutschland", "germany", "europe", "group", "gruppe", "holding", "international", "partner", "partners",
    "associates", "consulting", "consultants", "management", "capital", "advisory", "advisors", "corporate",
    "finance", "beratung", "private", "credit", "equity", "investment", "investments", "bank",
}


def firmenkern(name: str) -> set[str]:
    return {w for w in normalisiere(name).split() if len(w) >= 3 and w not in _RECHTSFORMEN}


def verbinde_dubletten(ba_stellen: dict, firmen_stellen: list[dict], cfg: dict) -> tuple[list[dict], int]:
    """Steht eine Firmen-Stelle auch bei der Arbeitsagentur, wird sie dort verknüpft.
    Verglichen werden Titel ohne Ortsnamen, Region und der Kern des Firmennamens."""
    index: dict[str, list[dict]] = {}
    for s in ba_stellen.values():
        index.setdefault(titel_schluessel(s["titel"], cfg), []).append(s)
    eigene, doppelt = [], 0
    for fs in firmen_stellen:
        kandidat = next((s for s in index.get(titel_schluessel(fs["titel"], cfg), [])
                         if set(s["regionen"]) & set(fs["regionen"]) and firmenkern(s["firma"]) & fs["_kern"]),
                        None)
        if kandidat:
            doppelt += 1
            kandidat["quellen"] = sorted(set(kandidat["quellen"]) | {QUELLE_FIRMA})
            kandidat.setdefault("extern", fs["link"])
            kandidat.setdefault("_verbunden", []).append(fs["id"])
            # Weitere Standorte von der Karriereseite übernehmen
            kandidat["regionen"] += [r for r in fs["regionen"] if r not in kandidat["regionen"]]
            bekannt = {normalisiere(o) for o in [kandidat["ort"], *kandidat.get("weitere_orte", [])]}
            dazu = [o for o in [fs["ort"], *fs.get("weitere_orte", [])] if o and normalisiere(o) not in bekannt]
            if dazu:
                kandidat["weitere_orte"] = (kandidat.get("weitere_orte", []) + dazu)[:20]
        else:
            eigene.append(fs)
    return eigene, doppelt


def fuehre_zusammen(ba_stellen, firmen_stellen, alte_stellen, ausgefallen, neu_dabei, jetzt, heute, cfg,
                    erfolgreich=frozenset()):
    """Neue Stellen mit dem letzten Stand verbinden; liefert (stellen, anzahl_neu).

    neu_dabei: Quellen, die zum ersten Mal erfolgreich abgefragt wurden. Ihre Stellen
    gelten nicht als "gerade eben entdeckt", sondern erscheinen mit ihrem Datum.
    erfolgreich: Quellen, die in diesem Lauf erreichbar waren (für die Nachfrist).
    """
    stellen, neu = {}, 0
    # Stand früher bei Arbeitsagentur UND Karriereseite, ist die Anzeige bei der
    # Arbeitsagentur aber inzwischen weg, übernimmt die Karriereseite ihre Daten.
    frueher_doppelt: dict[str, list[dict]] = {}
    for s in alte_stellen.values():
        if s.get("herkunft", "ba") == "ba" and QUELLE_FIRMA in s.get("quellen", []):
            frueher_doppelt.setdefault(titel_schluessel(s.get("titel", ""), cfg), []).append(s)

    for stelle in list(ba_stellen.values()) + firmen_stellen:
        if "ids" in stelle:  # Stelle der BA: bekannte ID behalten
            ids = stelle.pop("ids")
            stelle["id"] = next((i for i in ids if i in alte_stellen), ids[0])
        sid = stelle["id"]
        v1_id = stelle.pop("_v1_id", None)
        verbunden = [i for i in stelle.pop("_verbunden", []) if i in alte_stellen]
        kern = stelle.pop("_kern", None)
        datum = date.fromisoformat(stelle["veroeffentlicht"]) if stelle.get("veroeffentlicht") else None

        alt = alte_stellen.get(sid) or (alte_stellen.get(v1_id) if v1_id else None)
        if alt is None and verbunden:
            alt = alte_stellen[verbunden[0]]
        if alt is None and kern is not None:
            alt = next((s for s in frueher_doppelt.get(titel_schluessel(stelle["titel"], cfg), [])
                        if set(s.get("regionen", [])) & set(stelle["regionen"])
                        and firmenkern(s.get("firma", "")) & kern), None)
        # Frühere IDs merken, damit gemerkte Stellen auf der Webseite erhalten bleiben
        frueher = set((alt or {}).get("alt", [])) | set(verbunden)
        if alt and alt.get("id"):
            frueher.add(alt["id"])
        if v1_id and v1_id in alte_stellen:
            frueher.add(v1_id)
        frueher.discard(sid)
        if frueher:
            stelle["alt"] = sorted(frueher)

        erster_lauf = stelle.get("herkunft", "ba") in neu_dabei
        if alt and alt.get("gesehen"):
            if alt.get("genau"):
                stelle["gesehen"], stelle["genau"] = alt["gesehen"], True
            else:
                # Nur Datum bekannt: das Veröffentlichungsdatum zählt (das frühere von beiden).
                stelle["gesehen"] = min(str(alt["gesehen"])[:10], (datum or heute).isoformat())
                stelle["genau"] = False
        else:
            neu += 1
            if datum and (erster_lauf or datum < heute - timedelta(days=1)):
                # Ältere Anzeige oder neue Quelle: Uhrzeit unbekannt, nur das Datum zählt
                stelle["gesehen"], stelle["genau"] = datum.isoformat(), False
            elif erster_lauf:
                stelle["gesehen"], stelle["genau"] = heute.isoformat(), False
            else:
                stelle["gesehen"], stelle["genau"] = jetzt.isoformat().replace("+00:00", "Z"), True
        stelle["veroeffentlicht"] = (datum or date.fromisoformat(str(stelle["gesehen"])[:10])).isoformat()
        stellen[sid] = stelle

    # Stellen aus dem letzten Lauf, die diesmal fehlen:
    # - Quelle ausgefallen: Die Stelle bleibt bis zu einer Woche (z. B. Seite umgezogen).
    # - Quelle erreichbar: Die Stelle bleibt noch NACHFRIST_STUNDEN, denn manche Seiten
    #   lassen Stellen zwischendurch aus. So verschwindet sie nicht und kommt als "neu" wieder.
    # - Quelle nicht mehr in firmen.toml oder Stelle passt nicht mehr zu den Einstellungen: weg.
    jetzt_text = jetzt.isoformat().replace("+00:00", "Z")
    grenze_ausfall = (heute - timedelta(days=7)).isoformat()
    grenze_nachfrist = (jetzt - timedelta(hours=NACHFRIST_STUNDEN)).isoformat().replace("+00:00", "Z")
    uebernommen = {i for s in stellen.values() for i in s.get("alt", [])}
    for sid, alt in alte_stellen.items():
        if sid in stellen or sid in uebernommen:
            continue
        herkunft = alt.get("herkunft", "ba")
        vermisst = str(alt.get("vermisst_seit") or jetzt_text)
        if herkunft in ausgefallen:
            behalten = vermisst >= grenze_ausfall
        elif herkunft in erfolgreich:
            behalten = vermisst >= grenze_nachfrist
        else:
            behalten = False
        if behalten and passt_noch(alt, cfg):
            stellen[sid] = {**alt, "vermisst_seit": vermisst}
    return stellen, neu


def passt_noch(stelle: dict, cfg: dict) -> bool:
    """Passt eine gerade fehlende Stelle noch zu den Einstellungen? (Ausschlussliste,
    Bereiche oder Regionen können seit dem letzten Lauf geändert worden sein.)"""
    if not all(feld in stelle for feld in PFLICHTFELDER):  # Eintrag aus einer älteren Version
        return False
    bereiche = {name for name, _ in cfg["bereiche"]}
    regionen = {r["name"] for r in cfg["regionen"]} | ({cfg["remote_region"]} if cfg["remote"] else set())
    return (not ist_ausgeschlossen(normalisiere(stelle.get("titel", "")), cfg)
            and bool(set(stelle.get("bereiche", [])) & bereiche)
            and bool(set(stelle.get("regionen", [])) & regionen))


# Felder, die jede Stelle braucht, damit die Webseite sie anzeigen und filtern kann
PFLICHTFELDER = ("titel", "link", "ort", "regionen", "bereiche", "arten", "stufen", "gesehen", "veroeffentlicht", "quellen")


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
    zeitstempel = jetzt.isoformat().replace("+00:00", "Z")

    alt = lade_alte_daten()
    alte_stellen = {s["id"]: s for s in alt.get("stellen", []) if isinstance(s, dict) and s.get("id")}
    alte_quellen = alt.get("quellen") or {}

    statistik: Counter = Counter()
    beispiele: dict = {"kein_bereich": Counter(), "ausgeschlossen": Counter()}
    protokoll: list[str] = []
    diagnose: dict = {}
    start = time.monotonic()

    # 1. Arbeitsagentur
    treffer, abfragen, fehlgeschlagen, endpunkt = sammle_arbeitsagentur(
        cfg, statistik, beispiele, protokoll, diagnose)
    if not endpunkt or abfragen == 0 or fehlgeschlagen == abfragen:
        status = "fehler"
    elif fehlgeschlagen:
        status = "teilweise"
    else:
        status = "ok"
    ba_stellen = baue_ba_stellen(treffer, cfg, heute)
    dauer_ba = time.monotonic() - start

    # 2. Firmen-Karriereseiten
    firmen_protokoll: list[str] = []
    firmen_stellen, firmen_bericht, ausgefallen = sammle_firmen(cfg, heute, firmen_protokoll)
    firmen_stellen, doppelt = verbinde_dubletten(ba_stellen, firmen_stellen, cfg)
    if status != "ok":
        ausgefallen.add("ba")
    firmen_fehler = sum(1 for b in firmen_bericht if b["status"] != "ok")
    firmen_status = ("ok" if not firmen_fehler else
                     "fehler" if firmen_fehler == len(firmen_bericht) else "teilweise") if firmen_bericht else "keine"

    # 3. Zusammenführen. Quellen, die zum ersten Mal dabei sind, bringen keine "neuen" Stellen.
    alte_firmen = alte_quellen.get(QUELLE_FIRMA + "n") or {}
    bekannt = set(alte_firmen.get("bekannt") or [])
    if alte_stellen or (alte_quellen.get(QUELLE_BA) or {}).get("letzter_erfolg"):
        bekannt.add("ba")
    erfolgreich = {b["herkunft"] for b in firmen_bericht if b["status"] == "ok"}
    if status != "fehler":
        erfolgreich.add("ba")
    neu_dabei = erfolgreich - bekannt
    stellen, neu = fuehre_zusammen(ba_stellen, firmen_stellen, alte_stellen, ausgefallen, neu_dabei,
                                   jetzt, heute, cfg, erfolgreich - ausgefallen)
    # Davon von Firmen, die gerade erst in firmen.toml aufgenommen wurden
    neu_von_neuen_firmen = sum(1 for sid, s in stellen.items()
                               if s.get("herkunft", "ba") != "ba" and s["herkunft"] in neu_dabei
                               and sid not in alte_stellen and not s.get("alt"))
    # Stellen in der Nachfrist: Quelle erreichbar, Stelle diesmal nicht geliefert
    in_nachfrist = [s for s in stellen.values()
                    if s.get("vermisst_seit") and s.get("herkunft", "ba") not in ausgefallen]

    ohne_ort = sum(1 for s in stellen.values() if not s.get("ort"))
    ohne_stufe = Counter(s["titel"] for s in stellen.values() if s.get("stufen") == [OHNE_STUFE])
    diagnose.update({
        "endpunkt": endpunkt,
        "ohne_ort": ohne_ort,
        "ohne_stufe": [t for t, _ in ohne_stufe.most_common(60)],
        "kein_bereich": [t for t, _ in beispiele["kein_bereich"].most_common(150)],
        "ausgeschlossen": [t for t, _ in beispiele["ausgeschlossen"].most_common(60)],
        "firmen": firmen_bericht,
        "nachfrist": sorted(f"{s.get('firma', '')}: {s.get('titel', '')}" for s in in_nachfrist)[:40],
    })

    regionen_liste = [r["name"] for r in cfg["regionen"]]
    if any(cfg["remote_region"] in s.get("regionen", []) for s in stellen.values()):
        regionen_liste.append(cfg["remote_region"])
    daten = {
        "version": 3,
        "stand": zeitstempel,
        "quellen": {
            QUELLE_BA: {
                "status": status,
                "abfragen": abfragen,
                "fehlgeschlagen": fehlgeschlagen,
                "letzter_erfolg": zeitstempel if status != "fehler" else (alte_quellen.get(QUELLE_BA) or {}).get("letzter_erfolg"),
            },
            QUELLE_FIRMA + "n": {
                "status": firmen_status,
                "firmen": len(firmen_bericht),
                "fehlgeschlagen": firmen_fehler,
                "letzter_erfolg": zeitstempel if firmen_status in ("ok", "teilweise") else alte_firmen.get("letzter_erfolg"),
                "bekannt": sorted((bekannt | erfolgreich) - {"ba"}),
            },
        },
        "bereiche": [name for name, _ in cfg["bereiche"]],
        "regionen": regionen_liste,
        "stufen": STUFEN + [OHNE_STUFE],
        "diagnose": diagnose,
        "stellen": list(stellen.values()),
    }
    if status == "fehler" and alt.get("diagnose"):
        daten["diagnose"] = {**alt["diagnose"], "letzter_fehler": protokoll[:5], "firmen": firmen_bericht}
    schreibe_daten(daten)

    # --- Bericht für das Protokoll bei GitHub ---
    dauer = time.monotonic() - start
    bereich_zahlen = Counter(b for s in stellen.values() for b in s["bereiche"])
    art_zahlen = Counter(a for s in stellen.values() for a in s["arten"])
    stufen_zahlen = Counter(x for s in stellen.values() for x in s.get("stufen", [OHNE_STUFE]))
    aus_firmen = sum(1 for s in stellen.values() if QUELLE_FIRMA in s.get("quellen", []))
    zeilen = [
        f"## Stellenradar – Lauf vom {jetzt.astimezone(BERLIN):%d.%m.%Y, %H:%M} Uhr",
        "",
        f"- Arbeitsagentur: **{status}** – {abfragen} Abfragen, {fehlgeschlagen} fehlgeschlagen, "
        f"Schnittstelle `{endpunkt or 'keine erreichbar'}`, Dauer {dauer_ba:.0f} s",
        f"- Karriereseiten: **{firmen_status}** – {len(firmen_bericht)} Firmen, {firmen_fehler} nicht erreichbar, "
        f"{aus_firmen} Stellen im Radar (davon {doppelt} auch bei der Arbeitsagentur), Dauer {dauer - dauer_ba:.0f} s",
        f"- Stellen im Radar: **{len(stellen)}**, davon neu in diesem Lauf: **{neu}**"
        + (f" ({neu_von_neuen_firmen} davon von neu aufgenommenen Firmen)" if neu_von_neuen_firmen else "")
        + (f", diesmal nicht geliefert (bleiben noch bis zu {NACHFRIST_STUNDEN} Std.): {len(in_nachfrist)}"
           if in_nachfrist else "")
        + f", ohne Ortsangabe: {ohne_ort}",
        f"- Verworfene Titel (Arbeitsagentur): {len(beispiele['kein_bereich'])} ohne passenden Bereich, "
        f"{len(beispiele['ausgeschlossen'])} durch die Ausschlussliste, {statistik['unlesbar']} unlesbare Einträge",
        "- Nach Bereich: " + (", ".join(f"{b} {n}" for b, n in bereich_zahlen.most_common()) or "–"),
        "- Nach Anstellungsart: " + (", ".join(f"{a} {n}" for a, n in art_zahlen.most_common()) or "–"),
        "- Nach Karrierestufe: " + (", ".join(f"{a} {n}" for a, n in stufen_zahlen.most_common()) or "–"),
    ]
    mit_treffern = sorted((b for b in firmen_bericht if b.get("im_radar")), key=lambda b: -b["im_radar"])
    if mit_treffern:
        zeilen.append("- Firmen mit Stellen im Radar: " + ", ".join(f"{b['name']} {b['im_radar']}" for b in mit_treffern))
    ohne = [b["name"] for b in firmen_bericht if b["status"] == "ok" and not b.get("im_radar")]
    if ohne:
        zeilen.append("- Firmen ohne passende Stelle in deinen Regionen: " + ", ".join(ohne))
    if beispiele.get("felder"):
        zeilen.append("- Felder der Schnittstelle: " + ", ".join(beispiele["felder"]))
    for schluessel, ueberschrift in (("kein_bereich", "Häufigste Titel ohne passenden Bereich"),
                                      ("ausgeschlossen", "Häufigste durch die Ausschlussliste verworfene Titel")):
        if beispiele[schluessel]:
            zeilen.append(f"- {ueberschrift}: " + "; ".join(t for t, _ in beispiele[schluessel].most_common(12)))
    if protokoll or firmen_protokoll:
        zeilen += ["", "**Hinweise:**"] + [f"- {p}" for p in protokoll + firmen_protokoll]
    berichte(zeilen, status)

    if status == "fehler":
        print("::warning::Die Arbeitsagentur konnte nicht abgefragt werden. Die bisherigen Stellen bleiben erhalten.")
    elif status == "teilweise":
        print(f"::warning::{fehlgeschlagen} von {abfragen} Abfragen sind fehlgeschlagen.")
    if firmen_fehler:
        print(f"::warning::{firmen_fehler} von {len(firmen_bericht)} Firmen-Karriereseiten waren nicht erreichbar.")


if __name__ == "__main__":
    main()
