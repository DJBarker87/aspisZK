# Stage 2: late complete emitted Result and output-lane helper

`NBN_LateResult.source` proves the complete emitted late encoder Result on every typed statement and every output length, with exact output states for WrongLength, AfterstateIndexMismatch, Snapshot errors, Afterstate errors and success. No child-success/validation/canonicality premise. It imports NBK_LiveResult.source/NBK_AfterstateResult.source; no inherited theorem changed or reproved. The header, same-child tail and source factor are checked separately. Native whole-encoder association remains OPEN.

`NBN_OutputLane.first_source/source` give exact emitted first-byte and lane Result on every raw eight-word digest. Reuses NBD's scanner and S2K digest bytes. The first-byte law has no canonicality restriction. Native DigestEncode remains a named lower dependency, not silently supplied.

`NBN_CallbackObstruction.registry_unconstrained/no_fixed_registry_law` check the U04 selection obstruction (NBN_U04_FINDING.md). This is a finding about the quantified configuration, not a deployed code counterexample.

Passes L013,L018,L022,L023,L025; full metrics/pins/axioms in receipts. Latest whole late law L025: exit0, 2.320552715973463s, peak5423504KiB,swap0; standard axioms only. L017 reached the default heartbeat limit during a broad factor proof. Replaced by separately checked NBN_LateFactor.raw_eq and NBN_LateResult.factor with structural bind congruence, without raising limits. L024's zero-buffer simp exceeded recursion depth: replaced by symbolic length-only simplification; no depth increase or huge-buffer normalization. Rejected drafts excluded from closure. One admitted scope at a time; no Kani/Rust launched.

No whole native member or headline premise is claimed closed. Frozen source/ELFs untouched, no keys.
