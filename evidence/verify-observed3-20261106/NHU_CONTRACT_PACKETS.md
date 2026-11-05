# NHU immutable helper contracts

These packets use the SMALL pure-record method with the retained emitted helper definitions and probe/model laws. No fresh reference extraction is claimed. No `stub_verified` is used. All contract `modifies` clauses are empty; every primary `proof_for_contract` has a matched inverted-ensures failure on the identical source snapshot. These are P6/D188 option-A reclassifications, never trust removals.

| Frozen helper | Positive / exact negative | Domain established by harness | Retained/emitted/reference association |
|---|---|---|---|
| cm31_mul_i | K031 / K032 | two raw limbs <2147483647 | NHU_MaskHelpers.cm_i and negWord_eq; reference is the same explicit swapped record with conditional negation |
| cm31_mul_r | K033 / K034 | two raw limbs <2147483647 | NHU_MaskHelpers.cm_r/rNative_eq; total natural add/sub laws; already CLOSED baseline row072, no double credit |
| mul_tower_basis | K035 / K036 | four raw limbs <2147483647, coordinate<4 | NHU_Tower.result and NHU_TowerPacket.table, supported by RefCase1/2/3. Exact four branch table; failed unified reference theorem excluded |
| semantic lift_m31 | K037 / K038 | every u32, no canonical restriction | NHU_Lift.result (L043); same literal two-record constructor as native reference |

Ordinary native body checks K002/004/008/029 and their controls are supporting diagnostics; the primary immutable-helper certificates are the contract pairs above. The pure Bool/record interface exemption in ruling(t) applies. No allocation, callback, digest or mutable-source interface is contracted here. No function-pointer value or writable static is reached by these harnesses; compiler warnings from unreachable frozen test code do not extend their claim.

Field product and square operations in enclosing cuts remain local opaque-call records. Their emitted total laws, exact same operands and domains are listed in NHU_STUBS.md. They are not contract-verified multiplication.
