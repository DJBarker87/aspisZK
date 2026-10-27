# Pool lifecycle scope handoff

Branch: codex/cx-pool-scope-20261026. Source anchor:
9c994f068cd3881f05fdf75288a6152286e6c490. Local commits only; no push.

## Exact established claim

Source-review classification, not a formal lifecycle theorem:
- Pinned Pool crate/entrypoint and complete11-live-handler dispatch table;
  feature-off routes, alternate writable roles, close/refund helpers, CPI,
  foreign-owner assignment, canonical commit/rollback and deployment boundaries.
- Only AS8C writes the Pool-owned192-byte ASC8; only admitted verifier TX1
  writes the verifier-owned1768-byte CP. ASQ8 is an instruction and ASF8 an
  in-memory public statement, not interchangeable stored checkpoints.
- No concrete accepted attacker-chosen checkpoint write found by inspection.

Deliverable: design/POOL-LIFECYCLE-SCOPE-20261026.md, inventory rows V0–R4,
exact same-key causal writer/retention statement, separate ASC8 origin/state
obligation, measured source envelopes and costed options. Recommend B, a
write slice plus exhaustive dispatch/role noninterference and actual runtime
history instance. Do not commission a fourth history-only wrapper.

## Assumptions and actual closure

Global rows removed: NONE. L094–L098/L180 remain OPEN. No new assumption or
trust item adopted; source-to-model, source-to-ELF, initial-state provenance,
fixed deployment/runtime, causal load association, oracle-log/query-budget and
endpoint obligations remain. Source review alone does not discharge them.
SDK route-B trust does not include CPI, resize, lamports or concurrency.
Option C would require explicit owner/security-contract adoption.

## Validation and freeze

PoolS_validate.py passed exit0: source hashes/sizes unchanged; all132/132/133
inherited verifier/default, verifier/devnet, Pool compiler inputs match;
scan sources match; exactly one row per inventory ID; allowed tracked diff;
whitespace check. PoolS_validation.json records revision and measured inspection
wall time. PoolS_source-pins.json records initial freeze; inherited-build-match
records hashes/sizes from Low2, not newly rebuilt artifacts.

Formal target/attempt/exit/wall/peakRSS/swap/deps/axioms fields: not applicable,
no new theorem or formal run. Lean0/20, Kani0/10, Rust0; no scope/reservation
or heavy process launched. No proof attempt timed out or was memory-killed.
Prior Hir_/Hiq_/Hist_ proofs and Low2 build receipts were reused only with
explicit historical limitations; no replay or live deployment verification.
The three required ELF pins are unchanged and listed fully in the design.
No shipped-file changes, so no rebuild trigger. No keys/accounts/funds touched.

Only PoolS_ evidence and the explicitly requested design file changed. No
session A, NP6_, F3K_, prover-rw or other cone files/worktrees modified.

## Remaining blocker and next deliverable

Complete the deployed runtime/Pool instance, with real genesis/assignment,
AS8C creation/copy, exclusion of every alternate writable role and close,
canonical rollback and SAME physical account causal TX1/TX2 association.
Then connect Hir_'s selected writer/load to actual source cuts and the existing
same-world proof/public binding experiment. Upstream lane state correctness
and final probability/runtime transport remain separate obligations.
