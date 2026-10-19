# Stellenradar

Persönliches Jobportal für Stellen in Wirtschaftsprüfung, Interner Revision,
Transaction Services/FDD, Restrukturierung, M&A, Debt Advisory, Private Equity
und Unternehmensbewertung.

**Webseite:** https://leonesw.github.io/jobportal/

## So funktioniert es

1. Jede Stunde startet GitHub automatisch den Ablauf „Stellen sammeln“
   (Datei `.github/workflows/stellen-sammeln.yml`).
2. `sammler.py` fragt die Jobsuche der Bundesagentur für Arbeit und die
   Karriereseiten der Firmen aus `firmen.toml` ab und liest deine Jobalarme
   (LinkedIn, StepStone, Indeed) aus einem eigenen Postfach. Es behält nur
   passende Stellen in deinen Regionen und speichert sie in `jobs.json`. Steht
   eine Stelle in mehreren Quellen, erscheint sie nur einmal.
3. Danach wird die Webseite (`index.html` + `jobs.json`) neu veröffentlicht.

Im Protokoll jedes Laufs (Reiter „Actions“ → Lauf anklicken) steht, wie viele
Stellen von jeder Quelle kamen und welche Firmen-Seiten nicht erreichbar waren.

## Jobalarme

Das Postfach für die Jobalarme ist ein eigenes Gmail-Konto. Adresse und
App-Passwort stehen als Secrets `RADAR_MAIL_ADRESSE` und `RADAR_MAIL_PASSWORT`
im Repository (Settings → Secrets and variables → Actions), nie in einer Datei.
Das Radar liest dort nur Mails von LinkedIn, StepStone und Indeed, nur lesend,
und speichert Links ohne persönliche Tracking-Angaben. Eine Stelle aus einem
Jobalarm bleibt 30 Tage im Radar (einstellbar in `einstellungen.toml`).
Die Einrichtung steht in der Anleitung „Stellenradar-Jobalarme.pdf“.

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
