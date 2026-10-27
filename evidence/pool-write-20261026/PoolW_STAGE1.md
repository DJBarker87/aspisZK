# PoolW stage 1: extraction coverage and isolated zero reference

Accepted formal results: lean/PoolW_ZeroSource.lean is the exact extracted Boolean-state P6 index-scan reference (empty Types import removed); PoolW_ZeroStep.lean proves symbolic step, false-stop and exhaustion equations. L001/L002 pass, each printed audit contains only propext, Classical.choice, Quot.sound. No native/source equivalence follows from these reference lemmas alone.

Direct extraction limits retained, with no unchanged failed full-Pool rerun:
- AENEAS003: caller AccountInfo indexing F2140 rejects type parameters containing mutable borrows, InterpStatements.ml:730.
- AENEAS006: actual root-crate encoder loop pure419-422, internal Unreachable, InterpAbs.ml:1955.
- AENEAS007: isolated pure planner, internal Not_found in InterpReduceCollapse.ml:1991.
- AENEAS001/002/004 corrected opaque record selections; AENEAS005 exits0 but coverage audit finds the three top-level external roots absent, so output is NOT accepted as their extraction. It is retained as excluded diagnostic output.
- AENEAS008 tiny reference early return needs Option language item; reference009 uses Boolean loop state and extracts fully. No toolchain/launcher repair or cap change.

P6 native comparison: KANI001 whole193-byte relational guard times out (90s harness,101.9637203909806s command,4645824KiB,swap0); excluded. Replacement splits metadata, borrow failure, size, all-zero/rent and occupied marker. KANI002-006 all fail shared Rust harness compilation (ProgramError moved between assertions); charged, excluded. Fixed-source KANI007 is a smaller borrow-conflict case and also times out (91.93765203899238s,3433324KiB,swap0). No rerun of either timed-out job unchanged. Further source gates pending.

Budget at this stage: Lean4 attempts (2 pass,2 development failures); Kani8 launched (008 pending);9 Charon and9 Aeneas extraction attempts, separately recorded. L003/L004 failed proof snapshots/audits with recovery sorryAx are excluded and never imported. Full per-attempt source/dependency hashes, revision, commands, exit/wall/RSS/swap/cgroup and audits are in receipts. Shared host uses the existing S2W launchers unchanged and coherent SInt2 object selection. Scopes6G high/8G max/swap0/64 tasks; Lean-M7000; optimized Rust. No full package replay.

Premises removed at deployed endpoint: NONE. New proved laws describe the extracted P6 reference only. Native borrowing, exact source/P6 coupling, caller/codec/planner/body effects, physical-key/canonical-action instance, phase2 frames and runtime-history instance remain open. No source attack found and no trust item added. No shipped source or harness module changed: isolated proof-crate byte-identical source spans are under PoolW_guard and PoolW_SLICES.json, unrelated to release compilation. Inherited ELF pins unchanged; no ELF rebuild trigger. No key/account/funds touched.
