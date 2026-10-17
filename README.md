# Stellenradar

Persönliches Jobportal für Stellen in Wirtschaftsprüfung, Interner Revision,
Transaction Services/FDD, Restrukturierung, M&A, Debt Advisory, Private Equity
und Unternehmensbewertung.

**Webseite:** https://leonesw.github.io/jobportal/

## So funktioniert es

1. Jede Stunde startet GitHub automatisch den Ablauf „Stellen sammeln“
   (Datei `.github/workflows/stellen-sammeln.yml`).
2. `sammler.py` fragt die Jobsuche der Bundesagentur für Arbeit und die
   Karriereseiten der Firmen aus `firmen.toml` ab, behält nur passende Stellen
   in deinen Regionen und speichert sie in `jobs.json`. Steht eine Stelle an
   beiden Stellen, erscheint sie nur einmal.
3. Danach wird die Webseite (`index.html` + `jobs.json`) neu veröffentlicht.

Im Protokoll jedes Laufs (Reiter „Actions“ → Lauf anklicken) steht, wie viele
Stellen von jeder Quelle kamen und welche Firmen-Seiten nicht erreichbar waren.

## Einstellungen ändern

Suchbegriffe, Regionen, Bereiche und die Ausschlussliste stehen in
`einstellungen.toml`, die abgefragten Firmen in `firmen.toml`. Datei anklicken,
oben rechts auf den Stift klicken, ändern und mit „Commit changes“ speichern.
Der nächste stündliche Lauf übernimmt die Änderungen.

## Dateien

| Datei | Zweck |
| --- | --- |
| `index.html` | Die Webseite mit Filtern und Sortierung |
| `jobs.json` | Die gesammelten Stellen (wird automatisch aktualisiert) |
| `sammler.py` | Das Sammel-Programm |
| `einstellungen.toml` | Suchbegriffe, Regionen, Bereiche, Ausschlüsse |
| `firmen.toml` | Firmen, deren Karriereseiten direkt abgefragt werden |
| `.github/workflows/stellen-sammeln.yml` | Die stündliche Automatik |
