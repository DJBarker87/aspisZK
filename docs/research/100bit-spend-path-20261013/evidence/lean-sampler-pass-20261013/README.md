# Sampler pass arithmetic focused result

`R1SamplerPass` defines a high-to-low digit-list `numeral`, proves that the
long-division process's `processedValue` is the corresponding fold, and shows
that the initial state's final quotient and remainder equal division and
modulo of that numeral. The quotient proof uses the process invariant and its
remainder bound. These are symbolic arithmetic statements only; they do not
identify a Rust implementation, fixed-width arithmetic, or any probability or
security property.

Final source: `lean/SamplerPass.lean`, SHA-256
`631e025882495fcc5b2a402b9b002edc594080269c37553fd165499e61b9e0dd`.
Imported source `lean/SamplerLongDivision.lean` has SHA-256
`6b0a35daf77c00c8cb45fe627b0e4fbdf07f50da714a3737dc045939f790ed8c`.
Base revision: `a7ff42dc8068119ba1aea4e7bda471a01177b5be`.

The focused compile ran on pinned NUC workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with
`compile-one.sh R1SamplerPass c`. Attempt c exited 0 in 0.72 s, peak RSS
1,608,016 KiB, swap 0, under `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0` and Lean threshold 5000 MB. `#print axioms` reports
`[propext]` for `process_processedValue` and `[propext, Quot.sound]` for
`initialState_process_quotient_remainder`. The object is
`objects/R1SamplerPass.olean` in that workspace.

Attempts a–b are retained with source hashes, logs, timing logs, and receipts;
they exposed proof-plumbing errors. Attempt c is the final green result.
