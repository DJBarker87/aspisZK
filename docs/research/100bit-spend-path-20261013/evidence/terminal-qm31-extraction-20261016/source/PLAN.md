# Terminal source extraction kit (prepared only)

This kit starts from an extraction-only forwarding function and calls the actual public source method unchanged. Production source copies are byte-for-byte, except the copied `aspis-statement/src/lib.rs` receives one feature-gated module declaration to expose the wrapper; its original bytes are retained at `input/provenance/aspis-statement-lib.rs`. The wrapper merely forwards to `Public::terminal_qm31`. The workspace has only `aspis-core` and `aspis-statement`, with their original crate manifests and source trees; the root workspace scaffold supplies package/dependency inheritance. The copied lock is retained and pinned.

Source revision recorded: `39cda89cc9e06961684ec5fd0209312b5c15ec29`. Current entry file SHA-256: `0a446a7df661cabcf6f4c38c079f9970b03f21a7351cb2878e6fb76c62ab1ca1`. Wrapper SHA-256: `53061be6d8bc1d0006a01c5501677cec6d963402442050e54fc86401a51717a0`. There are 137 source/manifest rows pinned; the core and statement trees total about 4 MB before scaffold/lock. `verify_kit.py` verifies copied source against the current worktree, except the documented single `lib.rs` module append.

## Entrypoint and path

`crate::extraction_probe::terminal_qm31_probe` takes the actual `r0::Public` enum, claims, alpha and `Challenges`, then calls `public.terminal_qm31`. That production method builds the selected 3×28 claims array, calls `terminal_parts`, and propagates its result. `terminal_parts` calls `composition_parts`. No source function is copied into a replacement body. The post-translation audit must verify those actual bodies (or trace any compiler inlining) appear in the generated target, and record opaque/external functions. An empty or wrapper-only LLBC/Aeneas result is a failed target audit.

Planned command vectors, not executed, are recorded in `input/planned-commands.json`. The selected-mask precedent uses pinned local tool binaries Charon `0.1.223` SHA `d785c5f18053c4d310c7388dfdb0b59adfc9854c28b632a34a8f6301ba1c4b43` and Aeneas `b59d518` SHA `fbb8dac1a9a57e635a762e04b95aeb46dbd2dab2be5ed54fa9e0b1321c1962cf`; the source precedent separately recorded NUC tool pins, so the root must pin an execution host/tool set and cap before launch. Planned Charon start is the free wrapper `crate::extraction_probe::terminal_qm31_probe`, with features `r0,pool-v1-kernel`, offline/locked/release. Aeneas output is target-namespaced and split-file, then declaration/callgraph audit is required.

## Likely translation limits

The reachable exact source includes an array construction, selector generation, Poseidon semantic evaluator, copy residual evaluator, and a reverse Horner fold. The source graph also contains `Result`/`Option` control flow, `core::array::from_fn`, iterator reverse loops, a dynamic 20-level append-transition loop, and `Option::is_some_and`. These are candidate translation friction points, not claims of failure. `aspis-core/build.rs` generates fixed/circle/line tables (including RATE512 windows), so compile time may include substantial build-script generation plus the statement/core crate compile before Charon and Aeneas. Keep that build work in the reviewed bounded scope.

If the complete public path fails translation, preserve the failed attempt. A focused `terminal_parts` follow-up would need an additional wrapper placed in the copied source module because it is private and depends on private `SemanticPublic`; that wrapper would bypass the public method's claims projection. Record that reduced boundary explicitly. Do not shim or rewrite any reachable production function.

## What this does not cover

This kit does not include `crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed`. It does not establish that the actual terminal equals `R0P.Mask.terminalZ` or that successful `verify_observed` implies `sumcheckChecksZ`. Those are subsequent source-refinement goals requiring transcript, parsed-claim, and ten-round loop correspondence. No Rust/Cargo build, Charon, Aeneas, or Lean job has been run.
