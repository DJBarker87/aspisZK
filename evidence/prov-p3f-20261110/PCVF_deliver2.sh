#!/bin/bash
python3 -I - <<'PY'
import json
cls={"schema":"PCVF_CLASSIFICATIONS/1","entries":[
 {"id":"PCVF-C1","case":"array_from_fn_copy bridge","classification":"stop item: the fresh core.array.from_fn is an axiom; a bridge equality is underivable. Fact stated exactly as PCVF_FromFn.FromFnBridge. Not made a trust row (the owner decision admits only SDK type models, the core slice iterator model and the constant-encoding line).","consequence":"23 dependants stay OPEN"},
 {"id":"PCVF-C2","case":"SDK/cross-crate externals of a parametric gate (AdapterRw.Ops, NMT_call_k)","classification":"result class CONDITIONAL_ON_BINDING, not EQUALITY_PROVED: the equality is proved for all externals; the identification of those externals with the frozen items is made where the gate is instantiated, and is not proved here. Satisfiability of the hypotheses is proved (bound_exists, binding_satisfiable).","consequence":"9 AdapterRw + 2 Port5Q2 + 2 NMT records move HAND_ADAPTED/OPEN to CONDITIONAL_ON_BINDING"},
 {"id":"PCVF-C3","case":"core-library callees that the emission declares as axioms (map_err, Result clone) in AdapterRw","classification":"resolved to the gate's definitions of the same name (existing practice for the 502 externals resolved by a gate constant); recorded as a retained assumption, no new trust row","consequence":"the AdapterRw results depend on the gate models of those two core functions"},
 {"id":"PCVF-C4","case":"type identification by name (AdapterRw, Port5Q2, NMT)","classification":"fresh text elaborated inside the gate's namespace so unqualified type names are the gate's; valid because the emission's Types.lean declarations have the same text (checked by reading; Error: discriminant attribute only). The per-type Equiv proofs were not redone here; NMT_stage1_owned OwnedAccount Types is still TEXT_IDENTICAL_ONLY in PCUJ_ALL_STATUS.","consequence":"retained"},
 {"id":"PCVF-C5","case":"iterative compile errors L003-L007 on the AdapterRw file","classification":"one shape corrected stepwise (missing Hash type in the gate, callee owner, include-variable argument); not repeated unchanged. L003-L005 sources contained a placeholder sorry and are kept only as .xz with sha256 (no .lean with sorry committed).","consequence":"none"},
 {"id":"PCVF-C6","case":"Port3 checked-versus-wrapping","classification":"known class (PCUJ-C3): three Port3 definitions need an OFF emission because the gate uses wrapping_mul/add/sub on plain operators; not re-examined. No new difference at a matching configuration was found in this run.","consequence":"Port3 left NOT_ATTEMPTED"},
 {"id":"PCVF-C7","case":"AspisR72Sampler gate-only helpers","classification":"reduce at the caller via P3b (reuse); not re-credited as definition-level equalities","consequence":"no status change"}]}
json.dump(cls,open('PCVF_CLASSIFICATIONS.json','w'),indent=1)
json.dump(cls,open('PCVF_CLASSIFICATION.json','w'),indent=1)
rem={"schema":"PCVF_REMAINING/1","target_established":False,"items":[
 {"item":1,"remaining":"23 array_from_fn dependants (RPu_FIq_Native04 x3, Native05 x7, Native07 x4, Native09 x4, Native10 x4, Native11 x1): need either a library definition of core::array::from_fn or the FromFnBridge fact; not a proof task for the Aeneas library as it stands."},
 {"item":2,"remaining":["Port3_NativeGeometryBody 28 HAND_ADAPTED (carrier FibreIndex=Usize in the gate; 20 externals; 3 need an OFF emission)","compact.OFF_* (6; gate constants are functions of an Ops instance)","Port4C already RECEIPTED"]},
 {"item":3,"remaining":["decode_k_value (new extraction shape or classification decision on an appended-scratch wrapper)","candidate_claims.claims","NJT_claims_ref (hash-linked route unchanged)","the five AspisR72Sampler helpers: covered at the caller by P3b, secure_ood_circle_point_from_parameter still open"]},
 {"item":4,"remaining_20":[
  "AspisR1TerminalDecoder decode_pool_v1_pair_verified_afterstate_v1 (needs a distinct emission shape)",
  "WideToBytes x4 (StdModel vs ChunksExactMut instances: bridge lemma needed)",
  "AspisR72Sampler secure_ood_circle_point_from_parameter (heartbeats in two shapes; callee-first with PRVC_LoopBridge, needs P3b R72 given/preamble)",
  "NJA_Multiproof node_count",
  "NMT_stage1_owned stage1_owned (17 NMT_call parameters: needs the callee-order table from the NMT gate generation)",
  "Port23PUSH BatchedWeights.push",
  "FIo_Native mul_by_r, heap.filled, Dot.push",
  "FIp_NativeDots four_dots family x5",
  "S1NativeCompact expand_semantic x3"]},
 {"item":5,"remaining":"array/slice, num/ops and discriminant helpers not examined"},
 {"item":6,"remaining":"S1ClaimBorrowedAbiNativeV1, S1ClaimBoundedResultCompositionV1, S1ClaimOwnedNestedModelV1 not reconstructed; S1ValuesOwnedModelV1 stays as reconstructed in P4c"}]}
json.dump(rem,open('PCVF_REMAINING.json','w'),indent=1)
hm={"schema":"PCVF_HAND_MODELS/1","note":"no hand model added; no trust row added","items":[
 {"name":"array_from_fn_copy","status":"unchanged hand model; bridge to the emission's axiom core.array.from_fn unprovable; fact stated as PCVF_FromFn.FromFnBridge; erasure and builder identity proved (PCVF_L002)"},
 {"name":"gate Ops / NMT_call_k boundary (AdapterRw, NMT)","status":"binding to the frozen externals remains the instantiation obligation; fresh=gate proved for all externals"},
 {"name":"Vec IterMut model (Port5Q2 intoIter)","status":"hypothesis hInto in weights_eq; this is the core slice iterator model class the owner decision admits as a trust row"},
 {"name":"gate models of core.result.Result.map_err, Result clone, Try.branch","status":"used in place of the emission's axioms in AdapterRw; recorded, no trust row"}]}
json.dump(hm,open('PCVF_HAND_MODELS.json','w'),indent=1)
tl={"schema":"PCVF_TOOLS/1","tools":[
 {"name":"PCVF_run.py","origin":"evidence/prov-p2j-20261110/PCUJ_run.py with PCUJ_ -> PCVF_, host workspace codex-pc-prov-p3f-20261110, comment fixed to Stream C < 2 (the code already enforced < 2)"},
 {"name":"PCVF_run_host.py","origin":"PCUJ_run_host.py renamed"},
 {"name":"PCVF_deliver.sh, PCVF_deliver2.sh","origin":"this job: writes the summary JSON from receipts"}],
 "generator":"PCUJ_gen_equalities.py was not run; the new files were written by hand from the emission text (external axioms to parameters), PCVF-C2/C4"}
json.dump(tl,open('PCVF_TOOLS.json','w'),indent=1)
PY
