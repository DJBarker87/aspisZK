# Focused typed-prefix parser check

`R1TypedPrefixParser` supplies a pure row-indexed parser over already
delimited records. The final `typed-prefix-d` attempt passed locally with
`lake env lean`: exit 0, 17.78 seconds, 2,830,811,136 bytes maximum process
RSS, 3,294,592 KiB sampled aggregate RSS, and zero swap operations. The
runner used Lean's 6,000 MB limit and stopped aggregate process-group RSS
above 7 GiB. No dependency build or build-host job ran.

The six printed declarations are `decode_append`, `decode_length`,
`decode_rows`, `decode_append_some`, `prefix_stable`, and `failure_persists`.
Every final axiom report contains only `propext` and `Quot.sound`.

Attempts a and b failed on syntax/proof errors; c passed the initial five
laws. Attempt d added the row-alignment theorem and removed an unused simp
argument. All four exact source snapshots, outputs, and measurements are
retained. The final source is new relative to base `136b746805f3438507732622c9b4e50f36bf49f9`;
its hash, the Mathlib revision/import pins, and the target object are recorded
in `source-manifest.json`.

These results do not implement semantic/circle/opening decoding, enforce a
25- or 33-row bound, parse raw streaming bytes, establish challenge/callback
stability, or connect to Rust verification. In particular, failure
persistence concerns an invalid list of complete records: truncated byte
strings can become valid when more bytes arrive. No full manifest replay
has been performed.
