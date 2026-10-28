# Native ELF scope handoff

**Answer: not as a blanket whole-program claim.** Native certificates use frozen source bytes, but their host target, optional feature selection, profile/checks and abstraction windows can differ from deployment. The exact three release artifacts have reproducible-build evidence under retained P7; this does not make every native bridge a verification of those ELFs. **The deployed100-bit target remains not established.**

## Findings and deliverables

- [NCR_FEATURE_TABLE.md](NCR_FEATURE_TABLE.md): differences first, exact realized release cfgs, per-family comparison,120 representative receipts across61 lanes and per-body conditional/assertion hits. Direct verifier-library Kani runs omit optimized-terminal; deployment enables it and selects different semantic/Copy bodies. Program-root Kani runs with release features are distinguished. Standalone kani-driver window rechecks are explicitly narrower than a frozen Cargo program compilation.
- [NCR_TARGET_DEPENDENT.md](NCR_TARGET_DEPENDENT.md): named reached SHA/PDA/Clock/return-data/CPI/log/allocator/entrypoint/layout interfaces and their trust rows; Pool's Solana-only transaction-level guard is absent on host. No claim of complete transitive SDK/std/Pool lifecycle coverage; unresolved lowerings remain explicit. Known Option<fn> quarantine and conservative historical candidates are retained without credit.
- [NCR_SOURCE_TO_ELF.md](NCR_SOURCE_TO_ELF.md): exact build-identity, loaded-program association and semantics-preservation statements, historical three-ELF reproductions and separate P7/Kani/P6/runtime/caller rows.
- [NCR_ATTEMPTS.jsonl](NCR_ATTEMPTS.jsonl): every own host attempt, including the failed stale historical runner path. No Kani or Lean invocation.

Fresh local checks: all587 inventoried function body hashes match the frozen source; all132/132/133 repository Rust compiler-input associations in Low2 match frozen4bb3b3f (157unique files). Ten locked SDK package archives match Cargo.lock checksums, and inspected source files equal archive bytes. No source/protocol/feature/toolchain/ELF adoption occurred. No assumption was discharged, added or widened. No cryptographic bound or failure event changed.

## Remaining concrete deliverables

1. For each enclosing semantic/prepare/caller certificate, bind its exact effective Cargo cfgs to the release-selected optimized bodies, or supply the exact already-proved equivalences with domains and source pins. An unaffected decoder/arithmetic helper may transfer locally; a shared source revision is insufficient for the enclosing call.
2. Record effective Kani rustc/debug/overflow configuration where receipts only give Cargo environment; prove release-domain no-overflow/debug-assert preservation and relevant accepted-run/effect transport. Do not add an assumed caller conclusion or fold this into compiler trust.
3. Associate actual syscall/ABI/allocator/SDK and Pool/CPI/stack-height execution to the named runtime rows. Keep known pointer-dependent results quarantined until independently validated; neither prefix renaming nor a different passing fixture clears them.
4. Maintain the exact pinned artifact/loaded-account/release-runtime association. No live cluster readback was requested or performed; program upgrade/version identity is not established by rebuilding.

The overall blocker is native selected-source/caller/runtime composition, not missing ELF hash equality. Existing Low2 L186 retirement under P7 and later native-bridge gaps are compatible statements. No new Lean theorem or axioms audit, full manifest replay, native/adversarial suite or security conclusion is claimed.

## Commits and resource accounting

Stage commits (local, no push):

- `abc5202abf` Record native and deployed compilation differences
- `ae44c96b78` Inventory target-dependent runtime and ABI boundaries
- `0a971541ed` State source-to-ELF obligation and retained compiler trust

Fresh reproduction and final validation are sealed below. All work is confined to this NCR evidence directory; crates/ and programs/ remain unchanged. No wallet/account key was deleted or cleaned up.

## Final sealed results

- Fresh default rebuild NCR_B003: exact pinned hash, exit0, build26.321091037s, scoped27.04s, RSS684,392KiB, cgroup peak2,438,955,008bytes, swap0. All156checked source/configuration inputs unchanged before/after. The four fresh selected-crate rustc cfg/codegen/target lists exactly equal the retained Low2 default lists. Devnet/Pool reproductions are reused historical evidence, not fresh runs.
- Host scopes5/6: NCR_I001 own stale-path failure before payload; NCR_I002 capped inspection; NCR_B003 optimized rebuild; NCR_I004 command collection and own cache cleanup; NCR_I005 generated-key permission retention. All admissions allowed:true AND exit0. Successful scopes have exact6G/8G/Swap0/Tasks64 caps. No Kani/Lean, timeout, memory kill, cap change or shared infrastructure repair.
- Own target cache was removed after terminal build. ELF/diagnostics and generated key remain on the host under `codex-cx-native-elfscope-20261028/NCR_B003/`. Key file is0600; contents were not read or committed, no funds/authority action or cleanup. No binary/object/archive committed.
- [NCR_VALIDATION.json](NCR_VALIDATION.json): focused local source/receipt consistency check exit0,1.021s,26,411,008-byte process peak RSS. It checks all required outputs, JSON/Python syntax, sampled configurations, frozen body/source associations, four fresh compiler configurations, artifact/caps/cleanup/key receipts, size limit and unchanged crates/programs. This is document/evidence validation, not a proof-manifest or formal axioms replay.
- Stage4 commit `3f0d0fdd7d` reproduces the pinned default ELF and retains exact build receipts; it corrects the superseded historical-runner stop in stage3 under rule11. Final handoff commit follows. No push.

No remaining host blocker. The remaining technical obligations are the selected-body/profile/caller/runtime associations above; this audit does not claim them discharged.
