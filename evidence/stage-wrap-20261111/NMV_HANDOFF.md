# NMV stage-wrapper handoff

IN PROGRESS. Target not yet established; no row credit requested. Branch codex/cx-stage-wrap-20261107. Owned rows TX1:344 stage1, TX2:240 stage2, and local snapshot helper. Only NMV modules and this evidence directory may change. Frozen source is 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool b936275465. No shipped source or trust-row changes.

Stage 0: route inspection identifies all three as guard-holding wrappers under (bm)(1); route is per-function ReviewedTranscription plus actual compiled function cuts under (bj)/(bl). The single permitted extraction confirmation is reserved for snapshot before any Kani. Full buffer content belongs in Lean under NLF SDK borrow/std laws. Native lengths are small or symbolic; no 1768+ byte arbitrary buffer will be materialized.

The fold carries original descriptors, cell identity/borrow tokens, owned snapshot metadata/bytes, ordered runtime/child events, full Rust Result replies, and stopped prefixes. stage1 writes only account2 data after owned-child success; a mismatched checkpoint length aborts after exclusive acquisition. stage2 clears return data before any snapshot, snapshots seven accounts, calls Clock::get, then forwards the complete owned-child Result. cu-profiling is OFF.

Children TX1:345 (NMT) and TX2:241 (NMS) have no committed prefix modules at stage-0 inspection. They remain full-strength RowSpec parameters, never assumed successful Results. A complete parameterized fold earns no row credit. Root instantiation requires a checked candidate/CLOSED child at SAME arguments.

Budget ceiling: 50 Lean/link/audit scopes, 60 Kani, one extraction confirmation. One capped scope at a time; 6G high/8G max/swap0/tasks64; Lean -M7000; optimized/offline native with frozen graph validation before every run. Host share count <6 and allowed:true plus exit0 admission required; free disk >=40GB. Existing host launchers remain unchanged. Own client is adapted from NMN, with corrected whole-host codex-* count and threshold six.

No security metric/contract change, wallet/key/account action, push, or release-artifact reproduction. Inherited default f8c0ec72…, devnet63ad3e9c…, Pool e0e49c34…. Exact formal validation/resource/axiom receipts will be appended as stages complete.
