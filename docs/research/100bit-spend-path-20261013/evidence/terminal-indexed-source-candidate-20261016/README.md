# Indexed terminal-source extraction candidate

This is an isolated modified-source candidate, not a release verifier. Relative to the retained from_fn-copy overlay, it replaces reverse-fold reconstruction with a descending index loop and replaces the final 33-cell mutable iterator with an ascending index loop. The source input, per-file manifest (the runner consumes `source_files`; inherited `source_file_rows` retain parent metadata), patches, exact runner, generated declarations and receipts are retained here.

The optimized Cargo build, Charon and Aeneas all succeeded on the NUC. Each stage ran under MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128; no stage had swaps or cgroup OOM events. Aeneas output is not itself a source-correctness theorem. Focused Lean proofs of the generated loops are separate consumers of these declarations.

The candidate base is `39cda89cc9e06961684ec5fd0209312b5c15ec29`, with the exact earlier helper overlays recorded in candidate-source-manifest.json. It changes two merged-source files; both indexed edits are in pair_forest_semantic_terminal.rs. Generated slices isolate the namespace and retain their own source pins.

If adopted, prove this candidate against the spend relation, integrate it into the current admitted source and perform the final source/artifact gates. Proving a superseded iterator implementation is not required to prove the new implementation; any claimed old/new behavioral equivalence requires its own evidence. No production source change or release claim is made by this archive.

| Stage | Exit | Wall seconds | Peak process RSS KiB | Peak swap bytes |
|---|---:|---:|---:|---:|
| build | 0 | 65.29 | 807004 | 0 |
| charon | 0 | 72.545 | 1103084 | 0 |
| aeneas | 0 | 8.946 | 300608 | 0 |
