# NMO field handling

No multiplication value is proved in Kani. No constrained arithmetic oracle is used to evade the job's full-havoc requirement. Full continuing arithmetic cuts remain OPEN at NMO-F1.

| Native stub | Role and domain | Lean association | Credit |
|---|---|---|---|
| NMO_unreachable_mul | Panic trap, terminal-Err partition only; entry is forbidden | NMO_ErrorFrontier.terminal_steps proves the source prefix ends at terminal/mapPublic; the native positive detects any actual trap entry | Reachability only, no multiplication value credit |
| NMO_unreachable_add | Same Err partition, no entered add | NMO_ErrorFrontier.terminal_steps | Reachability only |
| NMO_unreachable_mask | Same Err partition, no entered mask | NMO_ErrorFrontier.terminal_steps | Reachability only |
| Future full scalar mul cut | Canonical actual eta and stored terminal, internally derived | NMO_MulAtState.operands/product; retained NLU_Generated.emitted_mul and NLU_FieldValues.mul_value | No native cut yet |
| Future full scalar add cuts | Actual mask/product, then actual partial/extra[28], internally derived | NMO_ArithmeticAtState.source and NMO_ArithmeticFold.source, using retained NLU_FieldValues.add_value | No native cut yet |

The panic traps never stand in for an entered field operation or a value law. Their explicit purpose is to exclude downstream scanning/arithmetic even from the symbolic preprocessing graph on an Err partition. Retired K013/K014/K015 receive no credit. See NMO_CUTMAP.md and NMO_FAILING_STEP.md for the missing channels and exact scope of the prefix certificates. Source theorem credit follows only current successful receipts, not this table's planned names.
