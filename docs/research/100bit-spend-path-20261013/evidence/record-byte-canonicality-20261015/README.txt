Actual final-F 32-byte decoder check.

byte-a: exit1, 24.889 s, 2520944 KiB sampled, process swaps0.
The byte-read and wrong-length facts passed. The list-to-Fin8 canonicality
conversion lacked final singleton quantifier simplification; resulting
sorryAx audits are failed-check diagnostics, not accepted theorem results.
System-wide swap usage increased during byte-a; receipt retains both values.

byte-b: exit0, 17.317 s, 2802096 KiB sampled, process swaps0.
Maximum process RSS2236710912 bytes. All four public axioms reports have
only propext, Classical.choice and Quot.sound. One unnecessary-<;> lint
is retained; no unchanged proof replay was run just to remove it.
System-wide swap usage decreased during the passing check.

Both runs used a4GiB sampled process-group stop and Lean -M3500, readonly
final-F generated caches and the checked constructor predecessor object.
The snapshots, exact command/receipt, Lean --version and all runtime dylib
hashes are retained; the bin/lean launcher is not a sufficient version pin.
No object or duplicate generated module is included. Runner cache paths
are local evidence, not a portable dependency bootstrap script.

The final snapshot equals lean/ExtractedRecordByteCanonicality.lean.
The extracted model theorem does not prove the Rust execution, high-zero
base-field guard, whole validator loop, prefix, or first-read boundaries.
