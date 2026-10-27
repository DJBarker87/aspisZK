# Resume5 workflow deviations

1. Env-J41216 was submitted to the dependency preflight before the failed
   ProducerTuple predecessor had been repaired. The missing object stopped it
   before any host scope; the ID is consumed, zero charged Lean attempts.
   Subsequent dependent queues check the preceding receipt before continuing.
2. Reporting correction: an interim commentary estimated that the first lane2
   reservation retry had been early. The actual admission receipts show
   2026-10-27T04:58:37.956165+00:00 and 2026-10-27T05:01:45.634302+00:00: elapsed187.678137s, which
   satisfies180s. The estimate was wrong; no wait-policy violation occurred.
   Both refusals launched no scope/compiler/solver and are uncharged. The next
   attempt still waits a complete180s from the latest refusal with a fresh name.

All capped scopes in this resume have remained serial. These deviations do not
supply validation evidence, row credit, or endpoint-premise removal.

2. Forest Aeneas retry resume5-forest-r04 launched after150.660379seconds
   from r03 refusal rather than180. The preceding Python assertion failed,
   but the newline-separated shell continued to the next Python command.
   The retry was admitted and translated successfully; caps were unchanged
   and the preceding Charon scope was absent. This is a real wait-rule
   deviation, not a compliant wait. A driver-level fail-closed wait guard is
   added before any subsequent compile/extraction/native admission so a shell
   continuation cannot bypass it. The receipt remains charged as executed.
