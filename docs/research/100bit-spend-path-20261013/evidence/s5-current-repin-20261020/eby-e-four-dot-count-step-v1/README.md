# EbyE four-Dot checked count step

This focused Lean target proves the four-call EbyEDot source-shaped step and its count/range consequences. On successful `pushWithOps`, it derives the four successful raw Dot updates in the source order `ac, bd, ad, bc`; the count theorem derives the numeric successor and preserves the pre-call accumulator range from the actual count guard.

The Lean body uses explicit operation parameters for `fromWide`, Dot raw update, and checked Usize addition. The exact current Rust `EbyEDot::push` was extracted and its generated files are included for provenance, but the emitted Funs body has not yet been proven equal to this parameterized Lean body. In particular, concrete `Q::from_wide` binding remains open. The generated external template is retained only for provenance and is not imported or compiled. This packet makes no whole-caller or EbyE product claim.

The four direct Lean owners' exact sources and producer receipts/configs are included under `dependencies/`; compiled objects are intentionally omitted. The target's exact v11 source, config, preflight, command, Lean log, and resource receipt are under `lean/`. The separate exact-source extraction bundle and logs are under `extraction/`.
