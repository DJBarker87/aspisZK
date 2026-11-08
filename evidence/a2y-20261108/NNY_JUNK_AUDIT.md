# Y0 Returns choices

Before: `NNH_Libraries.tx2Value` uses `authValues.auth` at an off-domain 064 call. Returns places no constraint there; an Ok value cannot supply Dom064. After: use `NNY_JunkAudit.value = NNH_Stage2GuardedEval.value`; its off-domain choice is `.error .Checkpoint`. `NNY_JunkAudit.returned` proves Returns for the SAME frozen 241 Ref, and `auth_domain` recovers Dom064 from a successful guard. No RSL, library, or merged evaluator is edited.

The selected 241 Returns chain is `NNH_Stage2Eval.returned` -> `NNH_ValidateEval.returned` -> `NNH_AuthEval.returned/body_returned` -> `NNH_RegistryEval.returned`, `NND_LaneReturned.returned`, and the concrete Pool/V2 Values. Choices and call discharges:

| Site | Chosen value / discharge |
|---|---|
| 241 -> 242 | `NNH_ValidateEval.value`; Domain definition is True |
| 242 -> 233 | `NNH_AuthEval.value`; Domain is True |
| 233 -> 234 | `NNH_RegistryEval.value`; Domain is True |
| 233 -> 217 | `NND_LaneReturned.value`; Domain is True |
| 241 -> 064 | before: `authValues.auth`; after: guarded auth, error Checkpoint off-domain |
| 241 index accounts 0 and 6 panic | `indexValue = option ... invalidArgument`, an error on none |
| Pool scanner length overflow panic | error invalidAccountData (`NNY_JunkAudit.scan_panic`) |
| Pool reconstruction inverse-carrier failure panic | error invalidAccountData (`NNY_JunkAudit.reconstruct_panic`) |
| Pool scanner model fail/div fallback | raw Err InvalidAccountData, mapped to error |
| Pool reconstruction model fail/div fallback | raw Err InvalidAccountData, mapped to error |
| Pool emission non-return fallback | error invalidInstructionData |

Registry's immutable/v1 branches have no Spec.call or Spec.panic; all PDA misses choose error invalidAccountData. Lane decode misses choose error invalidAccountData. Master/checkpoint decode Boxes, live-snapshot Box, cloning and returned-error logging have allocation aborts; their value is the actual subsequent value and not a panic/call junk choice. Pool encode uses the actual optional result (no panic choice). The V2 law's observation evaluator chooses error Checkpoint on non-return; no successful value is manufactured on stops. The successful path is therefore not inferred from unguarded off-domain Returns.

L001: exit 0, 24.837 s, RSS 6806972 KiB, swaps 0. Four audited roots use only standard axioms (full output retained). This is evaluator hygiene, not model transport or A2 closure.
