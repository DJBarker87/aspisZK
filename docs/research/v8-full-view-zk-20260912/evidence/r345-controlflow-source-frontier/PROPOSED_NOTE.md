# R345: ControlFlow translator frontier archive (draft)

This scratch-only archive contains exact recursive copies of the R334 projection, R338 translation attempt, R339 projection, and R343 translation attempt. The independent inventory compares relative paths, sizes, and SHA-256 for every file; all 52 files match their originating scratch trees byte-for-byte.

R334 and R339 are metadata-only LLBC projections over the same R327 input SHA-256 `9ed7c0ab…d03442`. Their projection hashes are `8b9bd55e…1a69ca` (three selected methods: Fun37/39/40) and `0860e617…325417d` (Fun39 only). The saved audits report unchanged retained decoded source rows and hash-cons values, no missing or unknown recognized references, and no synthesized declarations or order entries. They retain source declaration ordering where present and keep the original rows whose metadata lacks an order entry. R334’s rejected pre-hash-cons-walk attempt and all other projection history are included in the recursive copies.

R338 used translator binary SHA `fff37170…60f4f`, runner SHA `183990ed…dedfd`, source revision `37d5dd7ecb2c6f7b98822147522b043884ef77d9`, and a 5G/7G/zero-swap/128-task scope. Translation exited 2 after 0.18 s at 54,032 KiB RSS with no generated output. It failed while translating selected Fun40: `Not allowed to expand enumerations with several variants`, at Rust `core/src/ops/control_flow.rs` line 131.

R343 used the same translator binary, runner SHA `a5d033ef…59287`, and recorded translator source revision `2e1ece93ae5834f2586ae5f6f75cd0f9856ab801`, under the same caps. Translation exited 2 after 0.21 s at 55,440 KiB RSS with no generated output. Aeneas reported a generated-name collision between `ControlFlow<(), ()>` and `ControlFlow<(), Infallible>` at the same Rust declaration span.

Both translation records are failures, not Lean runs; axioms are not applicable. This archive records current ControlFlow translation obstacles only. It does not prove source guards, source semantics, fold/extend behavior, or complete batch execution. All negative and incomplete artifacts are retained. Lead review is pending.
