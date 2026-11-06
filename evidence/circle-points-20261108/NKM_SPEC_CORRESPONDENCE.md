# Natural specification correspondence

The specification helpers are assumptions on field replies, not Kani field-arithmetic proofs. Their inputs and outputs are the same four canonical u32 limbs as the reached frozen call. NKM_NaturalLaws proves the following interpretation; NKM_SpecMatching connects raw ZERO/ONE tests to field equality.

|Rust natural helper|Lean interpretation / justification|
|---|---|
|ns_add(a,b)|ZMod.val_add, NKM_NaturalLaws.base_add: (a+b) mod P|
|ns_sub(a,b)|NKM_NaturalLaws.base_sub: (a+P-b) mod P; base_bounds proves subtraction is defined|
|ns_mul(a,b)|ZMod.val_mul, NKM_NaturalLaws.base_mul; base_bounds proves the u64 product does not wrap|
|ns_cm|NKM_NaturalLaws.cm_product: (ac-bd,ad+bc), i²=-1|
|rbd in ns_product|NKM_NaturalLaws.rotation: (2u-v,u+2v)=(2+i)(u+vi)|
|ns_product|NKM_NaturalLaws.tower_product: (ac+(2+i)bd,ad+bc), u²=2+i|
|ns_plus / ns_minus|coordinate base_add/base_sub, paired emitted add/sub laws|
|inverse kind2|NKM_SpecMatching.native_inverse_relation; NKM_SpecLaws.inverse_spec and inverse_unique; None iff zero, Some canonical and product ONE|

The split specification uses wrapping machine operations only where base_bounds proves equality with natural operations on the entire canonical domain. No overflow outcome is suppressed on a domain where it could occur.

Actual emitted multiplication, rather than merely the installed external, is paired by NKM_EmittedMul.emitted_exact. This derives an exact successful GenQ result from the canonical owner's generated_qm_mul_eq_probe and current_qm_mul_exact. toGen/toLocal are four unchanged word projections; gen_roundtrip proves their carrier identity. The explicit generated-body equality is the JFv law retargeted to its canonical RPu owner, not a duplicate field definition.

Other CLOSED callee rows retained from NKH: TX1:024 add, :029 mul, :032 square (NGH_QSquareOps.source / NGH_QSquareRef.model_eq), :033 sub, :034 try_inv (NHH_QAll.try_association, NHH_QBridge.try_packet, NHH_QTrace.source, NHH_StubDomains.qm_log). NKM_FieldLaws.closed_inverse transports the complete emitted inverse Result; inverse_zero/nonzero and inverse_unique provide the natural value on the caller's canonical domain. Native/source/emitted pins of those unchanged CLOSED rows are inherited, never reassigned to a changed function body.

The native parent G cuts are universally quantified over canonical replies. Specializing them to these proved replies is (y)(3)/(aq)(5), with no successful-child or endpoint premise. K025 is excluded; K026/K028 isolate and control the assumed-spec boundary instead of rerunning its timed-out whole shape. This split route and its exact transcriptions are visible to the next ledger reviewer; it is not reported as a passing K025 replay.
