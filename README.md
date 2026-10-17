# Stellenradar

Persönliches Jobportal für Stellen in Wirtschaftsprüfung, Interner Revision,
Transaction Services/FDD, Restrukturierung, M&A, Debt Advisory, Private Equity
und Unternehmensbewertung.

**Webseite:** https://leonesw.github.io/jobportal/

## So funktioniert es

1. Jede Stunde startet GitHub automatisch den Ablauf „Stellen sammeln“
   (Datei `.github/workflows/stellen-sammeln.yml`).
2. `sammler.py` fragt die Jobsuche der Bundesagentur für Arbeit ab, behält nur
   passende Stellen und speichert sie in `jobs.json`.
3. Danach wird die Webseite (`index.html` + `jobs.json`) neu veröffentlicht.

## Einstellungen ändern

Suchbegriffe, Regionen, Bereiche und die Ausschlussliste stehen in
`einstellungen.toml`. Datei anklicken, oben rechts auf den Stift klicken,
ändern und mit „Commit changes“ speichern. Der nächste stündliche Lauf
übernimmt die Änderungen.

## Dateien

| Datei | Zweck |
| --- | --- |
| `index.html` | Die Webseite mit Filtern und Sortierung |
| `jobs.json` | Die gesammelten Stellen (wird automatisch aktualisiert) |
| `sammler.py` | Das Sammel-Programm |
| `einstellungen.toml` | Suchbegriffe, Regionen, Bereiche, Ausschlüsse |
| `.github/workflows/stellen-sammeln.yml` | Die stündliche Automatik |
