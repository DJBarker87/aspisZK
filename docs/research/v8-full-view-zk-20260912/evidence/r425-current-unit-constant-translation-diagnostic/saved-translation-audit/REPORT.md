# R425 main build and translation diagnostic audit

PASS — Saved R425 main-build and single-translation diagnostics only; no reruns. Translation failed before generating Lean source; no formal or source-correspondence theorem is claimed.

The R425 main executable build passed in 1.74 s, peak RSS 334792 KiB, zero swaps; its recorded executable SHA256 is `eadb205f…ca9b01`. The single translation used unchanged R419 and R396 inputs with the reviewed namespace and flags. It exited 2 in 0.77 s, peak RSS 142032 KiB, zero swaps. Aeneas stopped at the mutable-borrow copy failure for `Iterator::next` (Rust span `iterator.rs:78:4–78:45`; compiler `InterpExpressions.ml:234`). No generated Lean or JSON manifest was produced. The translation has no Lean axiom report; the OCaml build axiom field is N/A.
