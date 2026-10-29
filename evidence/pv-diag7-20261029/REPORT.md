# PV_DIAG7 — D458 / option B diagnostic dataflow

Work in progress. Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`, branch `codex/pv-diag7-20261029`, base `444380cd27`. No implementation or endpoint/trust definition edits.

D215 / V400 is the single shared option-B P row: reached environment failure must be witness-independent. The signal is public to both experiments, with the complete observer and the existing error bound. This job distinguishes the deterministic fixed-signal diagnostic dataflow from the still-open native independence/transport obligation. It does not silently identify Boolean failure-event independence with independence of errno, configuration, error content or a whole outcome schedule.

`PV_DIAG7_Signal` records typed write/flush/file/errno outcomes and environment/configuration/error-string inputs. It contains no witness-formatted operands, user logger implementation, panic payload, captured frames, registers or crash memory. Public invocation operands and order are separate. `V400_OptionB_P` is an explicitly sufficient same-coordinate source formulation, NOT a newly proved native P row or a new trust item.

65703 failed due to proof indentation; 65704 failed because a lambda application needed beta reduction before rewriting. Both rejected sources are retained and uncredited. Corrections precede any dependent compile. Final validation and sink dispositions will be appended.

## Focused validation before final audit

97 Lean attempts have launched. Failed/uncredited IDs: 65703, 65704, 65748, 65753, 65757, 65758, 65759, 65770, 65783. All were followed by changed proof text or changed source/dependency inputs before use. No rejected object is consumed. The refined file signal preserves the reservation success bit; the separate nonce wrapper retains reset-to-None and error-kind storage. `PV_DIAG7_Write` instantiates the existing write-all model with real-valued success/error signals, keeping zero-write, Interrupted retry/drop and an explicit suffix, including every supplied finite prefix.

The pre-audit closure contains nine objects, zero source/object/dependency mismatches (`final-pre.json`). Native01 rejected an incorrect interpretation of inherited end-line labels; native02 locates each exact hashed body and checks its start line instead, and rechecks 17 regions. File contents and nonce-derived operands are not classified as environment outcomes. Native03 verifies the coherent closure; neither scope is a runtime privacy proof.
