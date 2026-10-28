# Reservation timing correction

Aeneas-16 refusal: 2026-10-27T11:52:10.121033 UTC.
Aeneas-17 refusal: 2026-10-27T11:55:03.015328 UTC.
The retry interval was 172.894295 seconds, 7.105705 seconds short of the
required 180 seconds. This was an orchestration timing error. Both were
refused; neither started a scope or consumed Lean/Kani budget. The next
retry must be no earlier than 11:58:03.015328 UTC. All other refusal waits
are retained in the individual receipts; no barrier was bypassed.
