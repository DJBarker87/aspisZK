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


## Stage 3 packet table

| Cut | Exact paired law/domain | Native scope |
|---|---|---|
| fields frontier child | NHG_FieldSpec.source + FieldBounds.source; nonempty prior Vec, <=8 raw words and len+4*n<=1880 | K027/K028 one row/counter boundary |
| root prefix children | Same fields packet; Native prefix checks routing only, not child state | K042/K043 |
| root tail fields/frontier | Same fields packet or FrontierPackets.closed_packets; actual entry len<=815 | K045/K046 one stage, full arbitrary prefix/suffix |
| public producer | ProducerPackets.source, both Public variants/all raw words; actual returned len<=1455 | K047/K048, exact ProducerError type |
| constructor new | inherited NGX SemanticNew/NewTrace; SAME borrowed producer Vec/hash/root | K047/K048; digest remains P1/RuntimeSyscall |
| begin semantic packet | inherited145, rows0..14 and SAME parsed Prefix frames5..3717 | retained K015/K021, BeginFrame/FrontComposition |

The initialized-tail oracles expose only bytes that exact_vec initialized
before truncating. u8 has no destructor; growth stays within that allocation.
They are arbitrary child-output envelopes containing the exact child law,
not copy implementations and not native child credit. General allocation
metadata/ownership/cleanup stays in the retained Std interpretation; there is
NO caller capacity1884 condition. KMX remains byte-identical and its actual
copy window K007/K019 plus AppendFrame composes all prefix/suffix values.

Future field-product oracle: Product.words/returns/canonical/natural proves
the exact emitted QM31.mul natural quartet on canonical operands. Native
semantic-value step is not yet attempted/admitted at this stage.
