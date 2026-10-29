# PV_DIAG7 — D458 / option B diagnostic dataflow

Work in progress. Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`, branch `codex/pv-diag7-20261029`, base `444380cd27`. No implementation or endpoint/trust definition edits.

D215 / V400 is the single shared option-B P row: reached environment failure must be witness-independent. The signal is public to both experiments, with the complete observer and the existing error bound. This job distinguishes the deterministic fixed-signal diagnostic dataflow from the still-open native independence/transport obligation. It does not silently identify Boolean failure-event independence with independence of errno, configuration, error content or a whole outcome schedule.

`PV_DIAG7_Signal` records typed write/flush/file/errno outcomes and environment/configuration/error-string inputs. It contains no witness-formatted operands, user logger implementation, panic payload, captured frames, registers or crash memory. Public invocation operands and order are separate. `V400_OptionB_P` is an explicitly sufficient same-coordinate source formulation, NOT a newly proved native P row or a new trust item.

65703 failed due to proof indentation; 65704 failed because a lambda application needed beta reduction before rewriting. Both rejected sources are retained and uncredited. Corrections precede any dependent compile. Final validation and sink dispositions will be appended.
