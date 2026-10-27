# Rejected leaf membership predicate, replaced by block casts

063 exit1,wall171.96760638104752s,peakRSS5747932KiB,swap0. This is a sequence of default200000-heartbeat declaration failures in canonical000..011, not a false byte equality, process wall-timeout or memory kill. Later recovery declarations are unvalidated. The source snapshot and errors are retained.

The whole162-byte membership predicate was too expensive under broad simp. The replacement removes those predicates entirely. It proves numeric cast equalities on each named64-byte block and34-byte tail using bounded rfl, then joins them by a separate generic append theorem. Hashes still use the original checked compression certificates. This is a permanent generator change. No depth/heartbeat/cgroup limit is increased; the failed predicate is not rerun unchanged. The previously checked HashBytes/Layout modules are preserved byte-identically; ByteAppend is a new module, so no inherited checked object is overwritten.
