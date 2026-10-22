import S3S9ConcreteFieldOpsV1
import S3S9ScalarFactorActualOpsStepV1
import TransparentFoldRangeLawV1
import S3S9TransparentFoldS2InstanceV1
import S2LibraFactoredIdentity
import S9FactoredLoopBodyShapeV3
import S9FactoredLoopTwoStepV4

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9TwoCallScalarMeaningV2
local instance selectedOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
open AspisR1S9HelperP6
open AspisR1S9TransparentFoldS2InstanceV1
open AspisR1.S2LibraFactoredIdentity

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev U := Std.Usize
abbrev E := AspisWideTower.WideExact
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM

def ScalarMeaning (p : W) (f : Array Q (4#usize))
    (out : field.WideExact) (seed : Q) : Prop :=
  ∃ (we : field.WideExact) (j0 j1 j2 j3 : U)
    (p0 p1 p2 p3 : field.WideExact) (q0 q1 q2 q3 : Q),
      Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 0#usize = .ok j0 ∧
      Array.index_usize p j0 = .ok p0 ∧ Array.index_usize f 0#usize = .ok q0 ∧
      Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 1#usize = .ok j1 ∧
      Array.index_usize p j1 = .ok p1 ∧ Array.index_usize f 1#usize = .ok q1 ∧
      Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 2#usize = .ok j2 ∧
      Array.index_usize p j2 = .ok p2 ∧ Array.index_usize f 2#usize = .ok q2 ∧
      Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize = .ok j3 ∧
      Array.index_usize p j3 = .ok p3 ∧ Array.index_usize f 3#usize = .ok q3 ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9CurrentFieldOpsV1.toE out) =
        scalar (scaled
          (readVector (AspisR1S9CurrentFieldOpsV1.decode p0)
            (AspisR1S9CurrentFieldOpsV1.decode p3)
            (AspisR1S9CurrentFieldOpsV1.decode p2)
            (AspisR1S9CurrentFieldOpsV1.decode p1))
          (AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER))
          (algebraMap ExactQM E
            (AspisR1CurrentWide.Proof.decodeQM
              (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM seed)))

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem concrete_factor_ops_eq :
    AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
      (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps) =
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps := by
  rfl

/-- Source suffix after the emitted scalar-factor call. It is copied from the
selected generated active body so the prefix theorem returns the actual
remaining `from_fn`, term reads, ordered additions, and side-specific updates. -/
def afterScalar [AspisR1S9HelperP6.FieldOps]
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : U)
    (iterNext : core.ops.range.Range U) (weights0 : W)
    (q4 q8 q12 q16 : Q) (low : field.WideExact) :
    Result (ControlFlow (core.ops.range.Range U × W) W) := do
  let (terms, _) ← core.array.from_fn 4#usize
    _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
    (ap1, Array.make 4#usize [field.QM31.ONE, q4, q8, q12])
  let we ← Array.index_usize terms 0#usize
  let we1 ← Array.index_usize terms 1#usize
  let first2 ← field.WideExact.add we we1
  let we2 ← Array.index_usize terms 2#usize
  let first3 ← field.WideExact.add first2 we2
  let we3 ← Array.index_usize terms 3#usize
  let all ← field.WideExact.add first3 we3
  if side = 0#usize then do
    let we4 ← field.WideExact.mul low all
    let weights1 ← Array.update weights0 0#usize we4
    let we5 ← field.WideExact.mul low first3
    let we6 ← field.WideExact.mul_qm31 we5 q16
    let a ← Array.update weights1 1#usize we6
    ok (cont (iterNext, a))
  else do
    let we4 ← Array.index_usize weights0 1#usize
    let i ← Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize
    let we5 ← Array.index_usize ap1 i
    let we6 ← field.WideExact.mul_m31 we5 _root_.AspisR1S9HelperP6.weights.QUARTER
    let we7 ← field.WideExact.mul low we6
    let we8 ← field.WideExact.add we4 we7
    let weights1 ← Array.update weights0 1#usize we8
    let we9 ← field.WideExact.mul low all
    let we10 ← field.WideExact.mul_qm31 we9 q4
    let weights2 ← Array.update weights1 2#usize we10
    let we11 ← field.WideExact.mul low first2
    let q3 ← field.QM31.mul q16 q4
    let we12 ← field.WideExact.mul_qm31 we11 q3
    let a ← Array.update weights2 3#usize we12
    ok (cont (iterNext, a))

/-- Invert the exact successful source prefix of one active iteration. It binds
the selected extra, actual four-entry kpowers result, q2/q4/q8/q12/q16
operations, and scalar-factor result, then returns the exact remaining body as
`htail`. -/
theorem active_body_scalar_prefix
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : U)
    (iterNext : core.ops.range.Range U) (weights0 : W)
    (flow : ControlFlow (core.ops.range.Range U × W) W)
    (hactive : @AspisR1S9FactoredLoopBodyShapeV3.activeBody
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      ap0 ap1 extra side iterNext weights0 = .ok flow) :
    ∃ (q q2 q4 q8 q12 q16 : Q) (q1 : Array Q (4#usize))
      (low : field.WideExact),
      Array.index_usize extra side = .ok q ∧
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) q = .ok q1 ∧
      Array.index_usize q1 2#usize = .ok q2 ∧
      field.QM31.square q2 = .ok q4 ∧ field.QM31.square q4 = .ok q8 ∧
      field.QM31.mul q8 q4 = .ok q12 ∧ field.QM31.square q8 = .ok q16 ∧
      @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        q1 ap0 = .ok low ∧
      @afterScalar AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        ap0 ap1 extra side iterNext weights0 q4 q8 q12 q16 low = .ok flow := by
  letI : Ops := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
  have hcur := hactive
  unfold AspisR1S9FactoredLoopBodyShapeV3.activeBody at hcur
  rcases bind_success_inv (Array.index_usize extra side) _ _ hcur with
    ⟨q, hq, hcur⟩
  rcases bind_success_inv (@weights.kpowers
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize) q) _ _ hcur with
    ⟨q1, hq1, hcur⟩
  rcases bind_success_inv (Array.index_usize q1 2#usize) _ _ hcur with
    ⟨q2, hq2, hcur⟩
  rcases bind_success_inv (field.QM31.square q2) _ _ hcur with
    ⟨q4, hq4, hcur⟩
  rcases bind_success_inv (field.QM31.square q4) _ _ hcur with
    ⟨q8, hq8, hcur⟩
  rcases bind_success_inv (field.QM31.mul q8 q4) _ _ hcur with
    ⟨q12, hq12, hcur⟩
  rcases bind_success_inv (field.QM31.square q8) _ _ hcur with
    ⟨q16, hq16, hcur⟩
  rcases bind_success_inv
      (@weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        q1 ap0) _ _ hcur with ⟨low, hlow, htail⟩
  have htail' : afterScalar ap0 ap1 extra side iterNext weights0
      q4 q8 q12 q16 low = .ok flow := by
    change @afterScalar AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      ap0 ap1 extra side iterNext weights0 q4 q8 q12 q16 low = .ok flow at htail
    exact htail
  exact ⟨q, q2, q4, q8, q12, q16, q1, low,
    hq, hq1, hq2, hq4, hq8, hq12, hq16, hlow, htail'⟩

/-- The same actual successful scalar call has the accepted S2 polynomial
meaning. Its `kpowers` success is derived by equating only the concrete
`kpowers` slot with the selected current model; no independent success premise
for that call is introduced. -/
theorem active_body_scalar_meaning
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : U)
    (iterNext : core.ops.range.Range U) (weights0 : W)
    (flow : ControlFlow (core.ops.range.Range U × W) W)
    (hactive : @AspisR1S9FactoredLoopBodyShapeV3.activeBody
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      ap0 ap1 extra side iterNext weights0 = .ok flow)
    (hp : ∀ (j : U) (x : field.WideExact), Array.index_usize ap0 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hextra : ∀ (j : U) (q : Q), Array.index_usize extra j = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q)) :
    ∃ (q q2 q4 q8 q12 q16 : Q) (q1 : Array Q (4#usize))
      (low : field.WideExact),
      Array.index_usize extra side = .ok q ∧
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) q = .ok q1 ∧
      Array.index_usize q1 2#usize = .ok q2 ∧
      field.QM31.square q2 = .ok q4 ∧ field.QM31.square q4 = .ok q8 ∧
      field.QM31.mul q8 q4 = .ok q12 ∧ field.QM31.square q8 = .ok q16 ∧
      @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        q1 ap0 = .ok low ∧
      @afterScalar AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        ap0 ap1 extra side iterNext weights0 q4 q8 q12 q16 low = .ok flow ∧
      ScalarMeaning ap0 q1 low q := by
  obtain ⟨q, q2, q4, q8, q12, q16, q1, low,
    hq, hq1, hq2, hq4, hq8, hq12, hq16, hlow, htail⟩ :=
    active_body_scalar_prefix ap0 ap1 extra side iterNext weights0 flow hactive
  have hrecord := concrete_factor_ops_eq
  have hlowConcrete :
      @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        q1 ap0 = .ok low := hlow
  have hinstalled :
      @weights.Weights.scalar_factor
        (AspisR1S9ScalarFactorActualOpsStepV1.installActualFactorOps
          (AspisR1S9TransparentFoldRangeLawV1.installExtractedFold
            AspisR1S9ConcreteFieldOpsV1.concreteFieldOps)) q1 ap0 = .ok low := by
    rw [concrete_factor_ops_eq]
    exact hlowConcrete
  have hcurrentPowers :
      @weights.kpowers AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
        (4#usize) q = .ok q1 := by
    simpa only [AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps] using
      (AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current (4#usize) q).symm.trans hq1
  obtain ⟨we, j0, j1, j2, j3, p0, p1, p2, p3, r0, r1, r2, r3,
      hperm0, hp0, hr0, hperm1, hp1, hr1, hperm2, hp2, hr2,
      hperm3, hp3, hr3, hvalue⟩ :=
    AspisR1S9TransparentFoldS2InstanceV1.scalar_factor_success_is_s2_scalar
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 q1 low q
      hinstalled hp (hextra side q hq) hcurrentPowers
  exact ⟨q, q2, q4, q8, q12, q16, q1, low,
    hq, hq1, hq2, hq4, hq8, hq12, hq16, hlow, htail,
    we, j0, j1, j2, j3, p0, p1, p2, p3, r0, r1, r2, r3,
    hperm0, hp0, hr0, hperm1, hp1, hr1, hperm2, hp2, hr2,
    hperm3, hp3, hr3, hvalue⟩

/-- From success of the exact two-iteration helper, both source-ordered active
calls expose their own actual kpowers and scalar-factor outputs with the
per-call S2 meaning. The returned witnesses keep the side-0 and side-1
arguments distinct; the second side index is obtained from the loop's actual
range iterator state. -/
theorem helper_success_two_scalar_meanings
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (initial output : W)
    (hp : ∀ (j : U) (x : field.WideExact), Array.index_usize ap0 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hextra : ∀ (j : U) (q : Q), Array.index_usize extra j = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q))
    (hloop : @weights.factored_s2_libra_weights_loop
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      AspisR1S9FactoredLoopTwoStepV4.start0 ap0 ap1 extra initial = .ok output) :
    ∃ (q0 q1 : Q) (high0 high1 : Array Q (4#usize))
      (low0 low1 : field.WideExact),
      Array.index_usize extra 0#usize = .ok q0 ∧
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) q0 = .ok high0 ∧
      @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        high0 ap0 = .ok low0 ∧ ScalarMeaning ap0 high0 low0 q0 ∧
      Array.index_usize extra 1#usize = .ok q1 ∧
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) q1 = .ok high1 ∧
      @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        high1 ap0 = .ok low1 ∧ ScalarMeaning ap0 high1 low1 q1 := by
  letI : Ops := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
  obtain ⟨iter1, iter2, middle, hnext0, hstart1, _, hbody0,
    hnext1, _, _, hbody1, _, _⟩ :=
    AspisR1S9FactoredLoopTwoStepV4.helper_success_two_body_calls
      ap0 ap1 extra initial output hloop
  have hactive0 := (AspisR1S9FactoredLoopBodyShapeV3.body_some_eq_activeBody
    ap0 ap1 extra AspisR1S9FactoredLoopTwoStepV4.start0 iter1
    0#usize initial hnext0).symm.trans hbody0
  have hstart1eq : iter1.start = 1#usize := by
    apply Std.UScalar.eq_of_val_eq
    exact hstart1
  have hactive1 : @AspisR1S9FactoredLoopBodyShapeV3.activeBody
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      ap0 ap1 extra 1#usize iter2 middle = .ok (.cont (iter2, output)) := by
    rw [← hstart1eq]
    exact (AspisR1S9FactoredLoopBodyShapeV3.body_some_eq_activeBody
      ap0 ap1 extra iter1 iter2 iter1.start middle hnext1).symm.trans hbody1
  obtain ⟨q0, _q20, _q40, _q80, _q120, _q160, high0, low0,
      hq0, hhigh0, _hq20, _hq40, _hq80, _hq120, _hq160, hlow0, _htail0,
      hmeaning0⟩ :=
    active_body_scalar_meaning ap0 ap1 extra 0#usize iter1 initial
      (.cont (iter1, middle)) hactive0 hp hextra
  obtain ⟨q1, _q21, _q41, _q81, _q121, _q161, high1, low1,
      hq1, hhigh1, _hq21, _hq41, _hq81, _hq121, _hq161, hlow1, _htail1,
      hmeaning1⟩ :=
    active_body_scalar_meaning ap0 ap1 extra 1#usize iter2 middle
      (.cont (iter2, output)) hactive1 hp hextra
  exact ⟨q0, q1, high0, high1, low0, low1,
    hq0, hhigh0, hlow0, hmeaning0,
    hq1, hhigh1, hlow1, hmeaning1⟩

#print axioms concrete_factor_ops_eq
#print axioms active_body_scalar_prefix
#print axioms active_body_scalar_meaning
#print axioms helper_success_two_scalar_meanings

end AspisR1S9TwoCallScalarMeaningV2
