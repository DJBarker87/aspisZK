# KNF opaque-leaf dependency audit

Stage 1; frozen Rust `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
This audits the thirteen distinct CLOSED leaf functions, not every historical
packet bearing LEAF in its name. Superseded OPEN packets do not add leaves.
INDEPENDENT means independent of the named K-2 quarantine, retaining all original
local domains, source/library/allocator/oracle qualifications and feature-parity
qualifications. It is not an enclosing driver or deployed headline proof.

| Leaf / authoritative packet | K-2 verdict | Quarantined support and exact property |
|---|---|---|
| `sampler::low_base_p_digits` — `leaf-sampler1-20261027/LPk_LEAF.md` | DEPENDENT | LPk_K011 `LPk_from_fn_order_word`: eight ordered closure calls, shared quotient capture, indexed digit stores and final capture. LPk_K014 `LPk_byte_decode`: all eight little-endian input words equal shift/or byte packing. Both are explicit checked-bridge rows consumed by the native trace. |
| `verifier::echeck` — `leaf-p6-10-20261027/LPl_echeck_LEAF.md` | INDEPENDENT | None. K001/K003 actual decoder/local Result, K002/K008 immutable windows, K009 caller sizes; inherited LPh K009/K010 and LPc K013–K016 concern iterator/tail laws, not the LPk sampler gates. The phrase “as in LPk” describes the hybrid method, not a sampler premise. |
| `compact::check_values` — `leaf-p6-10-20261027/LPl_check_values_LEAF.md` | INDEPENDENT | None. K005 decoder/Result, K006 immutable backing, K007 non-vacuity and inherited LPh K011; LPa/LPg fold laws are model laws. No wide_view inactive decoder or sampler observation is needed. |
| `r1_wire::validate_record_fields` — `leaf-p6-10-20261027/LPl_validate_record_fields_LEAF.md` | INDEPENDENT | None. Own per-chunk decoder/Result, iterator and row-shape gates plus symbolic first-error induction. No quarantined powers/parts/observer gate supplies a local obligation. |
| `verifier::checkpoint` — `kani-reverify5-20261028/KNE_FINDING.md`, KNE_Leaf.lean | INDEPENDENT | None in the current narrowed reached-S2/final_len64/weights64 route. Historical LPm checkpoint cited LPe_K019 (semantic-alpha and nested Z append traversal/frame). KNE replaces that append evidence with source-ordered bodyEmissions, 116 exact scheduled append transitions (43 inherited KND + 73 completed, including split windows), KNE_Writer.cohort_program_eq and KNE_Leaf.native_result. KNE_Model.bodyEmissions_payload and LPm_CheckpointBody.source_body are model identities, not imports of a Kani verdict. DriverEstablishedDomain and physical/source/library association remain explicit. The superseded arbitrary-growth LPm/KMX route is not counted. |
| `compact::expand_values` — `leaf-p6-12-20261027/LPn_expand_values_LEAF.md` | INDEPENDENT | None. LPn_K001 local window write/frame, K002 guards, inherited LPl K012 iterators and Lean spatial/trace induction. LPl's older OPEN packet is superseded. |
| `ValidatedRecord::decode_k` — `leaf-p6-12-20261027/LPn_decode_k_LEAF.md` | INDEPENDENT | None. Own K003/K005/K006/K008/K009/K010 guard, decoder, getter and selected-write facts. LPn_K008 is a Prefix getter and is distinct from quarantined LPo_K008. |
| `r1_semantic::claims` — `leaf-p6-12-20261027/LPn_claims_LEAF.md` | INDEPENDENT | None. Cites the preceding decode_k leaf and own allocation/owned-write/token gates; three same-record decodes and cleanup do not consume powers, sampler or Option<fn> observer results. |
| `canonical::Dot::push` — `leaf-p6-12-20261027/LPn_Dot_push_LEAF.md` | INDEPENDENT | None. Retained raw arithmetic support and LPi/LPf four wrapping-update induction. Importing LPi arithmetic support does not consume LPi_K015/K016 powers iteration gates; no powers array occurs in the Dot statement. |
| `candidate::wide_view` — `leaf-p6-13-20261027/LPo_wide_view_LEAF.md` | DEPENDENT | LPo_K008 `LPo_decode_words`: actual E::from_le_bytes success iff all eight input words < P, and every returned limb equals that same little-endian word. Other readset gates overapproximate the decoder and cannot replace this value/acceptance obligation. |
| `semantic_boundary` — `leaf-p6-13-20261027/LPo_semantic_boundary_LEAF.md` | INDEPENDENT | None. Same N28 array supplied by CLOSED LPn decode_k, own native fold/add routing and emitted field-value laws. It does not consume sibling wide_view or LPo_K008; its genuine Prefix decode support is LPn_K008. |
| `circle_sample` — `leaf-p6-14-20261027/LPp_circle_sample_LEAF.md` | DEPENDENT | Through explicitly reused LPk low-base-P bridge: LPk_K011 closure traversal/capture/indexed stores and LPk_K014 byte-word decode. LPp's own mapper/fallback/transcript context gates and R72 inverse proofs do not establish these sampler facts. The earlier LPo inverse-reference obstruction is superseded by the adopted R72 owner. |
| `verifier::prepared_claim` — `leaf-p6-18-20261027/LPt_prepared_claim_LEAF.md` | DEPENDENT | Through unchanged LPs/LPr/LPq consumer and LPm powers bridge: LPi_K015 `powers_final_iteration` final seventh write/full untouched-word frame and index7 early return; LPi_K016 `powers_continue_prefix` six continuing stores/frame, increment and next multiplication operands. Through LPq parts init/store row: LPm_K017 `parts_store`, six point+1 stores and complete seven-cell frame. LPm_K018 supplies initialization only. LPt's check/expand producer adapters discharge byte domains, not these native array obligations. No LPo_K008 dependency is added merely because wide_view is an enclosing caller; this leaf takes canonical inactive as its local input. |

## Tally and excluded chains

**9 INDEPENDENT, 4 DEPENDENT** before new KNF runs. Four distinct leaves need
six distinct quarantined properties: LPk_K011/K014, LPo_K008, LPi_K015/K016,
LPm_K017. LPk's two properties affect two leaves.

NBC_K001/K002 (mark/observer None), NBW_K026, KNB_K001, KNC_K003 and NCH_K049
are enclosing runtime/candidate observation chains. None is cited as a local
law by these thirteen authoritative bridges. They stay quarantined; this audit
does not clear or silently install any of them. LPe_K019 remains quarantined in
the historical checkpoint route; the current KNE route is the replacement
explicitly requested for this audit. Model theorem imports alone do not turn
an unrelated historical Kani harness into a premise.

Inspected authoritative LEAF packets, LPq's exact checked-stage table, inherited
LPm prepared/powers and LPi harness bodies, LPk/LPo harness snapshots, KNE model,
writer and final leaf, NCS_PARITY_AUDIT, KNB_FINDING and KNC_FINDING. No prover,
Rust or Kani invocation was needed for this source/evidence dependency audit.

## Subsequent disposition

The stage1 classifications above are preserved. KNF_FINDING.md records the
six matched static-form routes restoring all four DEPENDENT leaves. Final K-2
tally: nine standing credits plus four restored; none still dependent or failed.
Original pointer-form harnesses and enclosing runtime observer chains stay
quarantined.
