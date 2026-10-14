# Ordinary semantic decoder evidence

Source base: `c2a09bd56106565824dc28873c2b01b0fe8d8aea`.

Ten focused final targets connect the existing completion machinery to the
actual experiment for semantic rows 1 through 25. The source manifest records
22 attempts: 12 failed attempts retained for provenance and 10 final successful
attempts. Every attempt has an exact source snapshot and matching receipt/hash.

The final combined checkpoint passed in 1.41 s with peak RSS 3,528,532 KiB,
zero swap, and fifteen axiom reports restricted to `propext`, `Classical.choice`
and `Quot.sound`. All jobs used MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=128 and Lean's 5000 MB threshold. The same pinned
Linux workspace, Lean 4.32.0 toolchain and compiled cache were reused.

`source-manifest.json` records each target, source/object hashes, exact attempt
classification, resource receipt, runner and environment. The deterministic
final-object archive has SHA-256
`aead29064f9019636b3bfabc417954c574ae7e73076551cddc1fd311dd88a534`.

`ROOT-VALIDATION.json` records root's audit of all final and attempted source
hashes, compiler/resource logs, archive members, unchanged runner/environment
and fourteen runtime fingerprints. Root also inspected the final theorem
statements, premises and proof connections. `SHA256SUMS` seals all other files
in this directory.

These are case, parser and sampler-law connections. The full decoder dispatch,
security theorem instance, numerical bound, Rust/account correspondence and
privacy simulator remain open. See [the scope document](../../UNIFIED-SEMANTIC-DECODER.md).
