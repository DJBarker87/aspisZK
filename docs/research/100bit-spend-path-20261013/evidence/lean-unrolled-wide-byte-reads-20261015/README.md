# Unrolled wide parser byte-read lemma evidence

This focused bundle preserves attempts `unrolled-wide-byte-reads-a` and `-b` (failed) and `-c` (green) for `UnrolledWideByteReads`. The green source proves fixed 32-byte reads agree with the unrolled eight-limb parser and that the parser rejects wrong-length slices. Its three printed axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

The final source SHA-256 is `7dbe9fa03bb7219f3ce85f04b5a146f8fd1c1eb44135ec9c7d85bf9d0c95719a`. Attempt receipts record green exit 0, 2.02 seconds, 3,803,828 KiB peak RSS, zero swap, under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. The source revision is `aba310f1daa065a27da89d15c6c47166037a8a71`.

The three exact attempt snapshots, receipts, logs, timing data, runner files, environment base, direct and transitive import source/object pins, and final object are retained. `objects.tar.gz` contains the final target and its two direct imported modules and the transitive source module they depend on. `source-manifest.json` records hashes and all attempt statuses. This is a focused Lean result about the retained model; it does not prove Rust/compiler correspondence or broader verifier behavior. No target was rerun during collection.
