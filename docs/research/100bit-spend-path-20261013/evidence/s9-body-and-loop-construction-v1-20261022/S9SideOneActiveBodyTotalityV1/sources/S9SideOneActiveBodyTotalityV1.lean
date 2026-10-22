import S9SideHighPrefixTotalityV1
import S9SideZeroActiveBodyTotalityV1
import S9SideOneTailTotalV1
import S9FactoredLoopBodyShapeV3
import S9TwoCallScalarMeaningV1
import S9AfterScalarTermSumsV1
import S3S9ConcreteFieldOpsV1
import S3S9CurrentFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9SideOneActiveBodyTotalityV1

open AspisR1S9HelperP6
open AspisR1S9HelperP6PowerSemanticsV1

local instance selectedOps : FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev U := Std.Usize
abbrev Q := field.QM31
abbrev W := field.WideExact
abbrev FourW := Array W (4#usize)
abbrev TwoQ := Array Q (2#usize)
abbrev R := core.ops.range.Range U
abbrev Flow := ControlFlow (R × FourW) FourW

private theorem result_bind_assoc {A B C : Type}
    (m : Result A) (k : A → Result B) (h : B → Result C) :
    (do let b ← (do let a ← m; k a); h b) =
      (do let a ← m; let b ← k a; h b) := by
  cases m <;> rfl

private theorem helper_qm_eq_generated (q : Q) :
    helperToCurrentQM q = AspisR1S9GeneratedWideMulQM31V2.toQM q := by
  cases q <;> rfl

/-- The selected side-one active body is total when its actual source reads
are canonical. Its old slot 1 must be canonical because this branch reads and
adds it before its first write. The proof reuses the shared from_fn/addition
totality theorem and the exact side-one tail totality theorem. -/
theorem side_one_active_body_total
    (ap0 ap1 : FourW) (extra : TwoQ) (iterNext : R) (weights0 : FourW)
    (hap0 : ∀ (j : U) (x : W), Array.index_usize ap0 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hap1 : ∀ (j : U) (x : W), Array.index_usize ap1 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hextra : ∀ (j : U) (q : Q), Array.index_usize extra j = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q))
    (hold1 : ∀ (x : W), Array.index_usize weights0 1#usize = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x) :
    ∃ output,
      @AspisR1S9FactoredLoopBodyShapeV3.activeBody
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 ap1 extra
        1#usize iterNext weights0 = .ok (ControlFlow.cont (iterNext,output)) ∧
      AspisR1S9CurrentFieldOpsV1.Canonical
        (AspisR1.S9ArrayWriteScheduleRootV1.cells output 1) ∧
      AspisR1S9CurrentFieldOpsV1.Canonical
        (AspisR1.S9ArrayWriteScheduleRootV1.cells output 2) ∧
      AspisR1S9CurrentFieldOpsV1.Canonical
        (AspisR1.S9ArrayWriteScheduleRootV1.cells output 3) := by
  obtain ⟨seed,q1,q2,q4,q8,q12,q16,low,hseed,hq1,hq2,hq4,hq8,hq12,hq16,
    hlow,hq2Can,hq4Can,hq8Can,hq12Can,hq16Can,hlowCan⟩ :=
    AspisR1S9SideHighPrefixTotalityV1.side_high_prefix_total
      ap0 extra 1#usize (by decide) hap0 hextra
  obtain ⟨high,terms,we,we1,first2,we2,first3,we3,all,
      hhighEq,hfromfn,hwe,hwe1,hadd2,hwe2,hadd3,hwe3,haddAll,
      hfirst2Can,hfirst3Can,hallCan⟩ :=
    AspisR1S9SideZeroActiveBodyTotalityV1.from_fn_and_sums_total
      ap1 q4 q8 q12 hap1 hq4Can hq8Can hq12Can
  have hlowCan : AspisR1S9CurrentFieldOpsV1.Canonical low := hlowCan
  have hq4Side : AspisR1.S9ConcreteArithmeticAcceptedRootV1.CanonicalQ q4 := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q4)
    rw [← helper_qm_eq_generated]
    exact hq4Can
  have hq16Side : AspisR1.S9ConcreteArithmeticAcceptedRootV1.CanonicalQ q16 := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q16)
    rw [← helper_qm_eq_generated]
    exact hq16Can
  obtain ⟨output, htail, hcan1, hcan2, hcan3⟩ :=
    AspisR1.S9SideOneTailTotalV1.side_one_tail_total
      weights0 ap1 low all first2 q4 q16 hlowCan hallCan hfirst2Can
      hq4Side hq16Side hold1 hap1
  have hafter : @AspisR1S9TwoCallScalarMeaningV2.afterScalar
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 ap1 extra 1#usize
      iterNext weights0 q4 q8 q12 q16 low =
      .ok (ControlFlow.cont (iterNext, output)) := by
    unfold AspisR1S9TwoCallScalarMeaningV2.afterScalar
    rw [← hhighEq]
    rw [hfromfn]
    change (do
      let a ← Array.index_usize terms 0#usize
      let b ← Array.index_usize terms 1#usize
      let first2 ← @FieldOps.wideAdd selectedOps a b
      let c ← Array.index_usize terms 2#usize
      let first3 ← @FieldOps.wideAdd selectedOps first2 c
      let d ← Array.index_usize terms 3#usize
      let all ← @FieldOps.wideAdd selectedOps first3 d
      AspisR1S9AfterScalarTermSumsV1.afterSums ap1 1#usize iterNext
        weights0 low first2 first3 all q4 q16) = _
    simp only [hwe,hwe1,hadd2,hwe2,hadd3,hwe3,haddAll,bind_tc_ok]
    unfold AspisR1S9AfterScalarTermSumsV1.afterSums
    have hside : (1#usize) ≠ (0#usize) := by decide
    simp only [if_neg hside]
    have htailCont : (do
        let out ← AspisR1.S9SideOneTailRootV1.sideOneTail
          weights0 ap1 low all first2 q4 q16
        ok (ControlFlow.cont (iterNext, out))) =
          (Result.ok (ControlFlow.cont (iterNext,output)) : Result Flow) := by
      rw [htail]
      rfl
    simp only [AspisR1.S9SideOneTailRootV1.sideOneTail, result_bind_assoc] at htailCont
    exact htailCont
  have hactive : @AspisR1S9FactoredLoopBodyShapeV3.activeBody
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 ap1 extra
      1#usize iterNext weights0 = .ok (ControlFlow.cont (iterNext,output)) := by
    unfold AspisR1S9FactoredLoopBodyShapeV3.activeBody
    dsimp only [field.QM31.square, field.QM31.mul]
    rw [hseed]
    simp only [bind_tc_ok]
    rw [hq1]
    simp only [bind_tc_ok]
    rw [hq2]
    simp only [bind_tc_ok]
    rw [hq4]
    simp only [bind_tc_ok]
    rw [hq8]
    simp only [bind_tc_ok]
    rw [hq12]
    simp only [bind_tc_ok]
    rw [hq16]
    simp only [bind_tc_ok]
    rw [hlow]
    simp only [bind_tc_ok]
    exact hafter
  exact ⟨output,hactive,hcan1,hcan2,hcan3⟩

#print axioms side_one_active_body_total

end AspisR1S9SideOneActiveBodyTotalityV1
