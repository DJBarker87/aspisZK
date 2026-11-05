# NHG stubs

No arithmetic stub, writable static, function pointer oracle, or new digest realization.
Exact KMX patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; original source files pinned/copied unchanged. NHG_K001 did not reach verification.

| Stub | Paired value law / retained trust | Domain | Admission |
|---|---|---|---|
| KMX_copy_nonoverlapping | KMX_CopyMeaning existing laws | Copy elements, valid disjoint ranges | pending own matched control |
| KMX_to_vec | KMX_CopyMeaning existing laws | live initialized source slice | pending own matched control |
| KMX_extend_from_slice | FieldsRefinement431.extend_u8/extend_word and KMX_CopyMeaning; std/allocator realization retained | valid owned Vec, capacity arithmetic fits Usize | pending own matched control |
| KMX_realloc | exact retained KMX patch and successful-reallocation law, std/allocator realization retained | valid old allocation/layout; successful return | pending own matched control |

Digest VALUE remains P1/RuntimeSyscall existing H realization, not a new stub assumption. No multiplication is attempted in Kani.

## Selected stage2 controls and qualifications

K003/K017 no-growth; K005/K018 small-growth; K007/K019 raw realloc byte; K013/K020 complete semantic fields. Strict controls force the copied/newly written position and corrupt its expected byte/anchor word. The positive source configurations are unchanged by these control-only mutations; NHG_STRICT_CONTROL_PLAN.json and the validator check exact transformations.

The general-capacity bridge retains pinned Std reserve/allocation/capacity/ownership/cleanup interpretation, following NGC heap/resize. K003 capacity1884 is a local native witness, not a caller requirement. K007 and CopyFrame.grow_append4 supply the arbitrary-prefix value/frame induction. This is P6/D188 option-A reclassification; no metadata realization is removed.

| New oracle | Paired theorem / domain | Status |
|---|---|---|
| frontier fields post-Vec | NHG_FieldBounds.source (L030); same owned Vec, raw slice8,1<=len and len+32<=1880; full arbitrary logical Vec poststate within derived length envelope | native window in progress; parent OPEN |
| begin selected semantic call | CLOSED NGX semantic_validated packet, BeginPackets source substitution; same record/window/state, exact modifies state32/cursor, hash preserved | K015/K021 window passes/fails; frame composition L031, audit pending |
| semantic-value product_cut | NHG_Product.returns/canonical/natural (L032), generated_qm_mul_eq_probe and current_qm_mul_words; same canonical four-word operands | paired natural modular specification proved; native caller UNATTEMPTED, no credit |

Products use the NFT/NGH opaque-call-log method: no multiplication expression is evaluated or proved in Kani; the exact natural tuple is substituted in Lean. No unpaired arithmetic stub is selected for an admitted row.
