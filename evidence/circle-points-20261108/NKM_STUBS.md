# NKM field stub / domain table

The emitted external template is retained as evidence only and is never imported. NKM_circle.FunsExternal installs concrete adopted emitted field operations; it introduces no axiom. Native logs use local mutable records. Field arithmetic laws are proved only in Lean. No SHA/syscall or runtime value is modeled here.

|Native boundary|Specification|Named paired Lean law|Domain|
|---|---|---|---|
|square/event kind0|canonical natural QM31 product t*t|NKM_FieldLaws.square; NKM_SpecLaws.square_law|all four limbs < P|
|add/event kind1|coordinate sums modulo P|NKM_FieldLaws.add; NKM_SpecLaws.add_law|both operands canonical|
|sub/event kind3|coordinate (a+P-b) modulo P|NKM_FieldLaws.sub; NKM_SpecLaws.sub_law|both operands canonical|
|product/event kind4|CM31 tower product, u²=2+i, coordinates modulo P|NKM_EmittedMul.emitted_exact (actual generated body from canonical RPu/JFv); NKM_FieldLaws.mul; NKM_SpecLaws.product_law|both operands canonical|
|inverse/event kind2|None iff zero; Some canonical b with a*b=ONE|NKM_FieldLaws.inverse_zero/inverse_nonzero; NKM_SpecLaws.inverse_law/inverse_spec/inverse_unique; NKM_FieldLaws.closed_inverse|canonical denominator, including zero; never require denominator nonzero at entry|
|004 child|complete 006 Result, every error|NKM_Roots.circle; NKM_CircleModel.circle_source|same canonical parameter; caller sample theorem and encoded fallback constants|
|002 child|complete 004 Result, every error|NKM_Roots.ood; NKM_Adopted.ood|two canonical fixed parameters; c1≠0 and denominator certificate proved, not assumed|
|KMX_copy_nonoverlapping|exact committed KMX patch|unchanged KMX value laws; matched copy controls K011/K003 and K029/K030|valid disjoint Copy regions; no custom copy stub|

KMX patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Source files independently hashed by every native gate. Frozen dependency graph, all resolved crate features, offline mode and unchanged lock hash are recorded before/after every Kani run.

Natural spec source: NKM_natural_specs.rs.txt and NKM_NATURAL_OVERLAY.json; split replacement NKM_SPLIT_OVERLAY.json. Its base reductions, tower rotation/product and wrapping bounds must be checked by NKM_NaturalLaws. A pairing or native boundary that is not green remains OPEN; no stub-only pass is promoted.

Exact returned-Result calibration: K012 weak contract PASS, K013 inverted FAIL, K014 real-body assertion PASS, K015 unimplied assertion under stub_verified FAIL, K016 modifies violation FAIL. The only stub_verified use is this deliberately failing control. No opaque field multiplication is proved or substituted with a verified Kani multiplication contract.
