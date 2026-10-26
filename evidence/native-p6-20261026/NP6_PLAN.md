# Native P6 task

S2 OPEN; target not yet established. Rows L174, L177, L179 remain open.

Stage 1: exact shipped Claims and selected safe filled/boxed reference, arbitrary record contents, no Kani stubs. Prove full Result and output contents; distinguish allocator assumptions, ambient effects and successful-return scope.

Stage 2: interpret safe Vec/Box through the D188 standard model, derive slot laws and install the reference on the same joint accepted run. New Lean modules only, NP6_ prefix.

Stage 3: initial/pending actual-run interpretation, before/after statements, ledger delta, non-vacuity and success conditioning.

Frozen source pins are in NP6_start.json. No shipped changes are planned. New modules and receipts only. Reuse coherent SInt2 objects; 100 Lean attempts including dependencies and 40 Kani runs maximum. All host jobs use 6G high, 8G maximum, zero swap, 64 tasks; Lean -M7000 and optimized Rust. No package replay.
