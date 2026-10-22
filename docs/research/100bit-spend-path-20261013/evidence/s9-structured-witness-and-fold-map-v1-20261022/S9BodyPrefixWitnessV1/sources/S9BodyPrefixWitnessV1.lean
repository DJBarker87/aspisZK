import S9BodyPrefixRichV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9BodyPrefixSemanticsV1

open AspisR1S9HelperP6

/-- Structured, choice-backed view of the full generic rich prefix. The
constructor below is available only from a successful actual active-body
result and the existing source contracts. -/
structure BodyPrefixWitness
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : U)
    (iterNext : core.ops.range.Range U) (weights0 : W)
    (flow : ControlFlow (core.ops.range.Range U × W) W) where
  q : Q
  q1 : Array Q (4#usize)
  q2 : Q
  q4 : Q
  q8 : Q
  q12 : Q
  q16 : Q
  low : field.WideExact
  high : Array Q (4#usize)
  terms : W
  state : (W × Array Q (4#usize)) × U
  hterms : AspisR1S9HighTermsTraceV1.HighTermsFour ap1 high
  we : field.WideExact
  we1 : field.WideExact
  first2 : field.WideExact
  we2 : field.WideExact
  first3 : field.WideExact
  we3 : field.WideExact
  all : field.WideExact
  source : AspisR1S9FactoredLoopBodyShapeV3.activeBody
    ap0 ap1 extra side iterNext weights0 = .ok flow
  hq : Array.index_usize extra side = .ok q
  hkp : @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
    (4#usize) q = .ok q1
  hq2 : Array.index_usize q1 2#usize = .ok q2
  hq4 : @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q2 = .ok q4
  hq8 : @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q4 = .ok q8
  hq12 : @FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q8 q4 = .ok q12
  hq16 : @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q8 = .ok q16
  hscalar : @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
    q1 ap0 = .ok low
  scalarMeaning : AspisR1S9TwoCallScalarMeaningV2.ScalarMeaning ap0 q1 low q
  lowCanonical : AspisR1S9CurrentFieldOpsV1.Canonical low
  afterScalar : @AspisR1S9TwoCallScalarMeaningV2.afterScalar
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 ap1 extra side
    iterNext weights0 q4 q8 q12 q16 low = .ok flow
  highArray : high = Array.make 4#usize [field.QM31.ONE,q4,q8,q12]
  highCanonical : ∀ (j : U) (z : Q), Array.index_usize high j = .ok z →
    AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM z)
  highDecode : ∀ (j : U) (z : Q), Array.index_usize high j = .ok z →
    AspisR1S9HighPowerPrefixSemanticsV1.decodeQ z =
      AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q ^ (4 * j.val)
  q16Canonical : AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ q16
  q16Decode : AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q16 =
    AspisR1S9HighPowerPrefixSemanticsV1.decodeQ q ^ 16
  fromFn : @core.array.from_fn field.WideExact
    weights.factored_s2_libra_weights.closure
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize)
    weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
    (ap1, high) = .ok (terms, state)
  readWe : Array.index_usize terms 0#usize = .ok we
  readWe1 : Array.index_usize terms 1#usize = .ok we1
  addFirst2 : @field.WideExact.add AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we we1 = .ok first2
  readWe2 : Array.index_usize terms 2#usize = .ok we2
  addFirst3 : @field.WideExact.add AspisR1S9ConcreteFieldOpsV1.concreteFieldOps first2 we2 = .ok first3
  readWe3 : Array.index_usize terms 3#usize = .ok we3
  addAll : @field.WideExact.add AspisR1S9ConcreteFieldOpsV1.concreteFieldOps first3 we3 = .ok all
  first2Canonical : AspisR1S9CurrentFieldOpsV1.Canonical first2
  first2Decode : AspisR1S9CurrentFieldOpsV1.decode first2 =
    AspisR1S9AfterScalarTermSumsV2.decW we + AspisR1S9AfterScalarTermSumsV2.decW we1
  first3Canonical : AspisR1S9CurrentFieldOpsV1.Canonical first3
  first3Decode : AspisR1S9CurrentFieldOpsV1.decode first3 =
    AspisR1S9CurrentFieldOpsV1.decode first2 + AspisR1S9AfterScalarTermSumsV2.decW we2
  allCanonical : AspisR1S9CurrentFieldOpsV1.Canonical all
  allDecode : AspisR1S9CurrentFieldOpsV1.decode all =
    AspisR1S9CurrentFieldOpsV1.decode first3 + AspisR1S9AfterScalarTermSumsV2.decW we3
  afterSums : @AspisR1S9AfterScalarTermSumsV1.afterSums
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
    ap1 side iterNext weights0 low first2 first3 all q4 q16 = .ok flow

/-- Every successful active-body result builds one reusable structured
witness. Nonempty keeps the construction inside Prop; consumers select its
witness with classical choice, retaining the standard `Classical.choice` axiom. -/
theorem body_prefix_witness_nonempty
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : U)
    (iterNext : core.ops.range.Range U) (weights0 : W)
    (flow : ControlFlow (core.ops.range.Range U × W) W)
    (hactive : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra side iterNext weights0 = .ok flow)
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hextra : ∀ (j : U) (x : Q), Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x) :
    Nonempty (BodyPrefixWitness ap0 ap1 extra side iterNext weights0 flow) := by
  obtain ⟨q, q1, q2, q4, q8, q12, q16, low, high, terms, state, hterms,
      we, we1, first2, we2, first3, we3, all,
      hq, hkp, hq2, hq4, hq8, hq12, hq16, hscalar, hscalarMeaning,
      hlowCan, htail, hhighArray, hhighCan, hhighDecode, hq16Can, hq16Decode,
      hfromfn, hwe, hwe1, hadd2, hwe2read, hadd3, hwe3read, haddAll,
      hfirst2Can, hfirst2Dec, hfirst3Can, hfirst3Dec, hallCan, hallDec,
      hsums⟩ :=
    AspisR1S9BodyPrefixSemanticsV1.active_body_prefix_rich
      ap0 ap1 extra side iterNext weights0 flow hactive hp0 hp1 hextra
  exact ⟨{
    q := q, q1 := q1, q2 := q2, q4 := q4, q8 := q8, q12 := q12, q16 := q16,
    low := low, high := high, terms := terms, state := state, hterms := hterms,
    we := we, we1 := we1, first2 := first2, we2 := we2,
    first3 := first3, we3 := we3, all := all,
    source := hactive, hq := hq, hkp := hkp, hq2 := hq2, hq4 := hq4,
    hq8 := hq8, hq12 := hq12, hq16 := hq16, hscalar := hscalar,
    scalarMeaning := hscalarMeaning, lowCanonical := hlowCan,
    afterScalar := htail, highArray := hhighArray,
    highCanonical := hhighCan, highDecode := hhighDecode,
    q16Canonical := hq16Can, q16Decode := hq16Decode,
    fromFn := hfromfn, readWe := hwe, readWe1 := hwe1, addFirst2 := hadd2,
    readWe2 := hwe2read, addFirst3 := hadd3, readWe3 := hwe3read,
    addAll := haddAll, first2Canonical := hfirst2Can,
    first2Decode := hfirst2Dec, first3Canonical := hfirst3Can,
    first3Decode := hfirst3Dec, allCanonical := hallCan, allDecode := hallDec,
    afterSums := hsums
  }⟩

noncomputable def body_prefix_witness_of_success
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : U)
    (iterNext : core.ops.range.Range U) (weights0 : W)
    (flow : ControlFlow (core.ops.range.Range U × W) W)
    (hactive : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra side iterNext weights0 = .ok flow)
    (hp0 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap0 j = .ok x → AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hp1 : ∀ (j : U) (x : field.WideExact),
      Array.index_usize ap1 j = .ok x → AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hextra : ∀ (j : U) (x : Q), Array.index_usize extra j = .ok x →
      AspisR1S9HighPowerPrefixSemanticsV1.CanonicalQ x) :
    BodyPrefixWitness ap0 ap1 extra side iterNext weights0 flow :=
  Classical.choice (body_prefix_witness_nonempty ap0 ap1 extra side
    iterNext weights0 flow hactive hp0 hp1 hextra)

#print axioms body_prefix_witness_nonempty
#print axioms body_prefix_witness_of_success

end AspisR1S9BodyPrefixSemanticsV1
