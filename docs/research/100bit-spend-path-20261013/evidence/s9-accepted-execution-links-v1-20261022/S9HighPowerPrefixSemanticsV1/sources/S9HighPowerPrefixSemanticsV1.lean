import S9TwoCallScalarMeaningV1
import S3S9ConcreteSquareSemanticsV1
import S3S9ScalarFactorKpowersReadV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9HighPowerPrefixSemanticsV1

open AspisR1S9HelperP6
open AspisR1S9HelperP6PowerSemanticsV1

abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev W := Array AspisR1S9HelperP6.field.WideExact (4#usize)
abbrev Sem := AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics
abbrev CanonicalQ (x : Q) :=
  AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)
abbrev decodeQ (x : Q) :=
  AspisR1CurrentWide.Proof.decodeQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)

private theorem decodeQ_one : decodeQ field.QM31.ONE = 1 := by
  exact @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.decode_one
    AspisR1CurrentWide.Proof.ExactQM _
    AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps Sem

private theorem generated_to_current_qm (x : Q) :
    AspisR1S9GeneratedWideMulQM31V2.toQM x =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x := by
  cases x <;> rfl

private theorem index_success_bound {A : Type} {N : Std.Usize}
    (a : Array A N) (i : Std.Usize) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length :=
        (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

private theorem usize_eq_of_val_eq (a b : Std.Usize) (h : a.val = b.val) :
    a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp only [UScalar.val] at h
      have hab := BitVec.eq_of_toNat_eq h
      subst bv
      rfl

/-- Every successful active S9 body prefix supplies the exact same generated
`kpowers` result, q2 read, square results, and q8*q4 result consumed by the
high-term callback.  Under the existing canonicality contract for the selected
extra input, those actual returned values are canonical and decode to the
corresponding powers of that same seed.  No child-operation success is assumed
separately from the successful body witness. -/
theorem active_body_high_powers
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : Std.Usize)
    (iterNext : core.ops.range.Range Std.Usize) (weights0 : W)
    (flow : ControlFlow (core.ops.range.Range Std.Usize × W) W)
    (hactive : AspisR1S9FactoredLoopBodyShapeV3.activeBody
      ap0 ap1 extra side iterNext weights0 = .ok flow)
    (hextra : ∀ (j : Std.Usize) (x : Q),
      Array.index_usize extra j = .ok x → CanonicalQ x) :
    ∃ (q q2 q4 q8 q12 q16 : Q) (q1 : Array Q (4#usize))
      (low : field.WideExact) (high : Array Q (4#usize)),
      Array.index_usize extra side = .ok q ∧
      @weights.kpowers AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (4#usize) q = .ok q1 ∧
      Array.index_usize q1 2#usize = .ok q2 ∧
      @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q2 = .ok q4 ∧
      @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q4 = .ok q8 ∧
      @FieldOps.qmMul AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q8 q4 = .ok q12 ∧
      @FieldOps.qmSquare AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q8 = .ok q16 ∧
      @weights.Weights.scalar_factor AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        q1 ap0 = .ok low ∧
      AspisR1S9TwoCallScalarMeaningV2.afterScalar ap0 ap1 extra side
        iterNext weights0 q4 q8 q12 q16 low = .ok flow ∧
      high = Array.make 4#usize [field.QM31.ONE, q4, q8, q12] ∧
      (∀ (j : Std.Usize) (z : Q), Array.index_usize high j = .ok z →
        AspisR1CurrentWide.Proof.CanonicalQM
          (AspisR1S9GeneratedWideMulQM31V2.toQM z)) ∧
      (∀ (j : Std.Usize) (z : Q), Array.index_usize high j = .ok z →
        decodeQ z = decodeQ q ^ (4 * j.val)) ∧
      CanonicalQ q16 ∧ decodeQ q16 = decodeQ q ^ 16 := by
  letI : AspisR1S9HelperP6.FieldOps :=
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
  obtain ⟨q, q2, q4, q8, q12, q16, q1, low,
    hq, hq1, hq2, hq4, hq8, hq12, hq16, hlow, htail⟩ :=
    AspisR1S9TwoCallScalarMeaningV2.active_body_scalar_prefix
      ap0 ap1 extra side iterNext weights0 flow hactive
  have hseed : CanonicalQ q := hextra side q hq
  have hkpCurrent : @weights.kpowers currentQMOps (4#usize) q = .ok q1 := by
    exact (AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current
      (4#usize) q).symm.trans hq1
  obtain ⟨hcan2, hdec2⟩ :=
    AspisR1S9ScalarFactorKpowersReadV1.kpowers_success_read_current
      q q1 hseed hkpCurrent 2#usize q2 hq2
  have hdec2' : decodeQ q2 = decodeQ q ^ 2 := by
    simpa using hdec2

  obtain ⟨q4', hsq4, hcan4', hdec4'⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total q2 hcan2
  have hsq4' : @FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q2 = .ok q4 := by
    exact hq4
  have heq4 : q4' = q4 := Result.ok.inj (hsq4.symm.trans hsq4')
  change CanonicalQ q4' at hcan4'
  change decodeQ q4' = decodeQ q2 * decodeQ q2 at hdec4'
  rw [heq4] at hcan4' hdec4'
  have hcan4 : CanonicalQ q4 := hcan4'
  have hdec4 : decodeQ q4 = decodeQ q ^ 4 := by
    calc
      decodeQ q4 = decodeQ q2 * decodeQ q2 := hdec4'
      _ = decodeQ q ^ 4 := by rw [hdec2']; ring

  obtain ⟨q8', hsq8, hcan8', hdec8'⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total q4 hcan4
  have hsq8' : @FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q4 = .ok q8 := by
    exact hq8
  have heq8 : q8' = q8 := Result.ok.inj (hsq8.symm.trans hsq8')
  change CanonicalQ q8' at hcan8'
  change decodeQ q8' = decodeQ q4 * decodeQ q4 at hdec8'
  rw [heq8] at hcan8' hdec8'
  have hcan8 : CanonicalQ q8 := hcan8'
  have hdec8 : decodeQ q8 = decodeQ q ^ 8 := by
    calc
      decodeQ q8 = decodeQ q4 * decodeQ q4 := hdec8'
      _ = decodeQ q ^ 8 := by rw [hdec4]; ring

  have hmul12 : @FieldOps.qmMul currentQMOps q8 q4 = .ok q12 := by
    rw [← AspisR1S9ConcreteFieldOpsV1.concrete_qmMul_is_current]
    exact hq12
  have hcan12dec :=
    @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.mul_success
      AspisR1CurrentWide.Proof.ExactQM _
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps Sem
      q8 q4 q12 hcan8 hcan4 hmul12
  have hcan12 : CanonicalQ q12 := hcan12dec.1
  have hdec12 : decodeQ q12 = decodeQ q ^ 12 := by
    calc
      decodeQ q12 = decodeQ q8 * decodeQ q4 := hcan12dec.2
      _ = decodeQ q ^ 12 := by rw [hdec8, hdec4]; ring

  obtain ⟨q16', hsq16, hcan16', hdec16'⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total q8 hcan8
  have hsq16' : @FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps q8 = .ok q16 := by
    exact hq16
  have heq16 : q16' = q16 := Result.ok.inj (hsq16.symm.trans hsq16')
  change CanonicalQ q16' at hcan16'
  change decodeQ q16' = decodeQ q8 * decodeQ q8 at hdec16'
  rw [heq16] at hcan16' hdec16'
  have hcan16 : CanonicalQ q16 := hcan16'
  have hdec16 : decodeQ q16 = decodeQ q ^ 16 := by
    calc
      decodeQ q16 = decodeQ q8 * decodeQ q8 := hdec16'
      _ = decodeQ q ^ 16 := by rw [hdec8]; ring

  let high : Array Q (4#usize) :=
    Array.make 4#usize [field.QM31.ONE, q4, q8, q12]
  have hfour : (4#usize).val = 4 := by decide
  have hhighCan : ∀ (j : Std.Usize) (z : Q),
      Array.index_usize high j = .ok z → CanonicalQ z := by
    intro j z hread
    have hjbound := index_success_bound high j z hread
    have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
    rcases hjcases with hj | hj | hj | hj
    · have heq : j = 0#usize := usize_eq_of_val_eq j 0#usize (by simpa using hj)
      subst j
      have hz : z = field.QM31.ONE := by
        change (Result.ok field.QM31.ONE : Result Q) = Result.ok z at hread
        exact (Result.ok.inj hread).symm
      have hone := (@AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.one_canonical
          AspisR1CurrentWide.Proof.ExactQM _
          AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps Sem)
      change CanonicalQ field.QM31.ONE at hone
      subst z
      exact hone
    · have heq : j = 1#usize := usize_eq_of_val_eq j 1#usize (by simpa using hj)
      subst j
      have hz : z = q4 := by
        change (Result.ok q4 : Result Q) = Result.ok z at hread
        exact (Result.ok.inj hread).symm
      simpa [hz] using hcan4
    · have heq : j = 2#usize := usize_eq_of_val_eq j 2#usize (by simpa using hj)
      subst j
      have hz : z = q8 := by
        change (Result.ok q8 : Result Q) = Result.ok z at hread
        exact (Result.ok.inj hread).symm
      simpa [hz] using hcan8
    · have heq : j = 3#usize := usize_eq_of_val_eq j 3#usize (by simpa using hj)
      subst j
      have hz : z = q12 := by
        change (Result.ok q12 : Result Q) = Result.ok z at hread
        exact (Result.ok.inj hread).symm
      simpa [hz] using hcan12
  have hhighCanGenerated : ∀ (j : Std.Usize) (z : Q),
      Array.index_usize high j = .ok z →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM z) := by
    intro j z hread
    rw [generated_to_current_qm]
    exact hhighCan j z hread
  have hhighDecode : ∀ (j : Std.Usize) (z : Q),
      Array.index_usize high j = .ok z →
      decodeQ z = decodeQ q ^ (4 * j.val) := by
    intro j z hread
    have hjbound := index_success_bound high j z hread
    have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
    rcases hjcases with hj | hj | hj | hj
    · have heq : j = 0#usize := usize_eq_of_val_eq j 0#usize (by simpa using hj)
      subst j
      have hz : z = field.QM31.ONE := by
        change (Result.ok field.QM31.ONE : Result Q) = Result.ok z at hread
        exact (Result.ok.inj hread).symm
      simpa [hz, decodeQ_one] using (show decodeQ (field.QM31.ONE) = 1 from decodeQ_one)
    · have heq : j = 1#usize := usize_eq_of_val_eq j 1#usize (by simpa using hj)
      subst j
      have hz : z = q4 := by
        change (Result.ok q4 : Result Q) = Result.ok z at hread
        exact (Result.ok.inj hread).symm
      simpa [hz, hj, hdec4] using hdec4
    · have heq : j = 2#usize := usize_eq_of_val_eq j 2#usize (by simpa using hj)
      subst j
      have hz : z = q8 := by
        change (Result.ok q8 : Result Q) = Result.ok z at hread
        exact (Result.ok.inj hread).symm
      simpa [hz, hj, hdec8] using hdec8
    · have heq : j = 3#usize := usize_eq_of_val_eq j 3#usize (by simpa using hj)
      subst j
      have hz : z = q12 := by
        change (Result.ok q12 : Result Q) = Result.ok z at hread
        exact (Result.ok.inj hread).symm
      simpa [hz, hj, hdec12] using hdec12
  refine ⟨q, q2, q4, q8, q12, q16, q1, low, high,
    hq, hq1, hq2, hq4, hq8, hq12, hq16, hlow, htail, rfl,
    hhighCanGenerated, hhighDecode, hcan16, hdec16⟩

#print axioms active_body_high_powers

end AspisR1S9HighPowerPrefixSemanticsV1
