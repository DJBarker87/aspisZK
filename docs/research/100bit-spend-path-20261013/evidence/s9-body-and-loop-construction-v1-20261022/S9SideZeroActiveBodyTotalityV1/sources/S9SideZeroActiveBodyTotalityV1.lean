import S9AfterScalarTermSumsV1
import S9SideZeroHighPrefixTotalityV2
import S9HighTermsTraceV1
import S9HighTermsOneCallV2
import S9TwoCallScalarMeaningV1
import S9FactoredLoopBodyShapeV3
import S9SideZeroTailRootV1
import S3S9ConcreteFieldOpsV1
import S3S9CurrentFieldOpsV1
import S9ConcreteArithmeticAcceptedRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9SideZeroActiveBodyTotalityV1

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
abbrev decW (x : W) := AspisR1S9CurrentFieldOpsV1.decode x

private theorem result_bind_assoc {A B C : Type}
    (m : Result A) (k : A → Result B) (h : B → Result C) :
    (do let b ← (do let a ← m; k a); h b) =
      (do let a ← m; let b ← k a; h b) := by
  cases m <;> rfl

private theorem usize_eq_of_val_eq (a b : U) (h : a.val = b.val) : a = b := by
  apply UScalar.eq_of_val_eq
  exact h

private theorem array_four_bound {A : Type} (a : Array A (4#usize))
    (i : U) (x : A) (h : Array.index_usize a i = .ok x) : i.val < 4 := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length := (List.getElem?_eq_some_iff.mp hsome).1
      rw [a.property] at hlen
      simpa using hlen

private theorem terms_read_zero (terms : FourW)
    (t0 t1 t2 t3 : W) (hvals : terms.val = [t0,t1,t2,t3]) :
    Array.index_usize terms 0#usize = .ok t0 := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, hvals]
  rfl

private theorem terms_read_one (terms : FourW)
    (t0 t1 t2 t3 : W) (hvals : terms.val = [t0,t1,t2,t3]) :
    Array.index_usize terms 1#usize = .ok t1 := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, hvals]
  rfl

private theorem terms_read_two (terms : FourW)
    (t0 t1 t2 t3 : W) (hvals : terms.val = [t0,t1,t2,t3]) :
    Array.index_usize terms 2#usize = .ok t2 := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, hvals]
  rfl

private theorem terms_read_three (terms : FourW)
    (t0 t1 t2 t3 : W) (hvals : terms.val = [t0,t1,t2,t3]) :
    Array.index_usize terms 3#usize = .ok t3 := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, hvals]
  rfl

private theorem generated_to_current_qm (x : Q) :
    AspisR1S9GeneratedWideMulQM31V2.toQM x = helperToCurrentQM x := by
  cases x <;> rfl

private theorem generated_to_current_wide (x : W) :
    AspisR1S9GeneratedWideMulQM31V2.toWide x =
      AspisR1S9CurrentFieldOpsV1.toE x := by
  cases x <;> rfl

private theorem make_high_read_canonical
    (q4 q8 q12 : Q)
    (hq4 : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q4))
    (hq8 : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q8))
    (hq12 : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q12)) :
    ∀ (j : U) (q : Q),
      Array.index_usize (Array.make 4#usize [field.QM31.ONE,q4,q8,q12]) j = .ok q →
      AspisR1S9HighTermsTraceV1.canonicalQ q := by
  intro j q hread
  have hjbound := array_four_bound (Array.make 4#usize [field.QM31.ONE,q4,q8,q12]) j q hread
  have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases hjcases with hj | hj | hj | hj
  · have hidx : j = 0#usize := usize_eq_of_val_eq j 0#usize (by simpa using hj)
    subst j
    have hq : q = field.QM31.ONE := by
      change (Result.ok field.QM31.ONE : Result Q) = Result.ok q at hread
      exact (Result.ok.inj hread).symm
    subst q
    have hone := (@QMSemantics.one_canonical ExactQM _ currentFieldOps currentQMSemantics)
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM field.QM31.ONE)
    rw [generated_to_current_qm]
    exact hone
  · have hidx : j = 1#usize := usize_eq_of_val_eq j 1#usize (by simpa using hj)
    subst j
    have hq : q = q4 := by
      change (Result.ok q4 : Result Q) = Result.ok q at hread
      exact (Result.ok.inj hread).symm
    subst q
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q4)
    rw [generated_to_current_qm]
    exact hq4
  · have hidx : j = 2#usize := usize_eq_of_val_eq j 2#usize (by simpa using hj)
    subst j
    have hq : q = q8 := by
      change (Result.ok q8 : Result Q) = Result.ok q at hread
      exact (Result.ok.inj hread).symm
    subst q
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q8)
    rw [generated_to_current_qm]
    exact hq8
  · have hidx : j = 3#usize := usize_eq_of_val_eq j 3#usize (by simpa using hj)
    subst j
    have hq : q = q12 := by
      change (Result.ok q12 : Result Q) = Result.ok q at hread
      exact (Result.ok.inj hread).symm
    subst q
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q12)
    rw [generated_to_current_qm]
    exact hq12

theorem from_fn_and_sums_total
    (ap1 : FourW) (q4 q8 q12 : Q)
    (hap1 : ∀ (j : U) (x : W), Array.index_usize ap1 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hq4 : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q4))
    (hq8 : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q8))
    (hq12 : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q12)) :
    ∃ (high : Array Q (4#usize)) (terms : FourW)
      (we we1 first2 we2 first3 we3 all : W),
      high = Array.make 4#usize [field.QM31.ONE,q4,q8,q12] ∧
      @core.array.from_fn W weights.factored_s2_libra_weights.closure
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize)
        weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (ap1,high) = .ok (terms,((ap1,high),4#usize)) ∧
      Array.index_usize terms 0#usize = .ok we ∧
      Array.index_usize terms 1#usize = .ok we1 ∧
      @FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps we we1 = .ok first2 ∧
      Array.index_usize terms 2#usize = .ok we2 ∧
      @FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps first2 we2 = .ok first3 ∧
      Array.index_usize terms 3#usize = .ok we3 ∧
      @FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps first3 we3 = .ok all ∧
      AspisR1S9CurrentFieldOpsV1.Canonical first2 ∧
      AspisR1S9CurrentFieldOpsV1.Canonical first3 ∧
      AspisR1S9CurrentFieldOpsV1.Canonical all := by
  let high : Array Q (4#usize) := Array.make 4#usize [field.QM31.ONE,q4,q8,q12]
  have hhigh : ∀ (j : U) (q : Q), Array.index_usize high j = .ok q →
      AspisR1S9HighTermsTraceV1.canonicalQ q := by
    intro j q hread
    exact make_high_read_canonical q4 q8 q12 hq4 hq8 hq12 j q (by simpa [high] using hread)
  have hap1Generated : ∀ (j : U) (x : W), Array.index_usize ap1 j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x := by
    intro j x hread
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x)
    rw [generated_to_current_wide]
    exact hap1 j x hread
  obtain ⟨hterms⟩ := AspisR1S9HighTermsTraceV1.high_terms4_from_fn_p6
    ap1 high hap1Generated hhigh
  have hfromfn := hterms.generated_from_fn
  have hread0 := terms_read_zero hterms.terms hterms.call0.term hterms.call1.term
    hterms.call2.term hterms.call3.term hterms.terms_values
  have hread1 := terms_read_one hterms.terms hterms.call0.term hterms.call1.term
    hterms.call2.term hterms.call3.term hterms.terms_values
  have hread2 := terms_read_two hterms.terms hterms.call0.term hterms.call1.term
    hterms.call2.term hterms.call3.term hterms.terms_values
  have hread3 := terms_read_three hterms.terms hterms.call0.term hterms.call1.term
    hterms.call2.term hterms.call3.term hterms.terms_values
  have hwe0 : AspisR1S9CurrentFieldOpsV1.Canonical hterms.call0.term := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE hterms.call0.term)
    rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
    exact hterms.call0.term_canonical
  have hwe1 : AspisR1S9CurrentFieldOpsV1.Canonical hterms.call1.term := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE hterms.call1.term)
    rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
    exact hterms.call1.term_canonical
  have hwe2 : AspisR1S9CurrentFieldOpsV1.Canonical hterms.call2.term := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE hterms.call2.term)
    rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
    exact hterms.call2.term_canonical
  have hwe3 : AspisR1S9CurrentFieldOpsV1.Canonical hterms.call3.term := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE hterms.call3.term)
    rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
    exact hterms.call3.term_canonical
  obtain ⟨first2, hadd2, hcan2, _⟩ :=
    AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact
      hterms.call0.term hterms.call1.term hwe0 hwe1
  have hadd2' : @FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      hterms.call0.term hterms.call1.term = .ok first2 := by
    rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideAdd_dispatch]
    exact hadd2
  obtain ⟨first3, hadd3, hcan3, _⟩ :=
    AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact
      first2 hterms.call2.term hcan2 hwe2
  have hadd3' : @FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      first2 hterms.call2.term = .ok first3 := by
    rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideAdd_dispatch]
    exact hadd3
  obtain ⟨all, haddAll, hcanAll, _⟩ :=
    AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact
      first3 hterms.call3.term hcan3 hwe3
  have haddAll' : @FieldOps.wideAdd AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      first3 hterms.call3.term = .ok all := by
    rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideAdd_dispatch]
    exact haddAll
  exact ⟨high, hterms.terms, hterms.call0.term, hterms.call1.term, first2,
    hterms.call2.term, first3, hterms.call3.term, all, rfl, hfromfn,
    hread0, hread1, hadd2', hread2, hadd3', hread3, haddAll', hcan2, hcan3, hcanAll⟩

/-- Selected side-zero active-body totality from canonical inputs. It composes
the source-ordered scalar/power prefix, actual P6 high-term from_fn, three
ordered WideExact additions, and the exact side-zero checked-write tail. -/
theorem side_zero_active_body_total
    (ap0 ap1 : FourW) (extra : TwoQ) (iterNext : R) (weights0 : FourW)
    (hap0 : ∀ (j : U) (x : W), Array.index_usize ap0 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hap1 : ∀ (j : U) (x : W), Array.index_usize ap1 j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hextra : ∀ (j : U) (q : Q), Array.index_usize extra j = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q)) :
    ∃ output,
      @AspisR1S9FactoredLoopBodyShapeV3.activeBody
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 ap1 extra
        0#usize iterNext weights0 = .ok (ControlFlow.cont (iterNext,output)) ∧
      AspisR1.S9SideZeroTailRootV1.canonical
        (AspisR1.S9ArrayWriteScheduleRootV1.cells output 0) ∧
      AspisR1.S9SideZeroTailRootV1.canonical
        (AspisR1.S9ArrayWriteScheduleRootV1.cells output 1) := by
  obtain ⟨seed,q1,q2,q4,q8,q12,q16,low,hseed,hq1,hq2,hq4,hq8,hq12,hq16,
    hlow,hq2Can,hq4Can,hq8Can,hq12Can,hq16Can,hlowCan⟩ :=
    AspisR1S9SideZeroHighPrefixTotalityV2.side_zero_high_prefix_total
      ap0 extra hap0 hextra
  obtain ⟨high,terms,we,we1,first2,we2,first3,we3,all,
      hhighEq,hfromfn,hwe,hwe1,hadd2,hwe2,hadd3,hwe3,haddAll,
      hfirst2Can,hfirst3Can,hallCan⟩ :=
    from_fn_and_sums_total ap1 q4 q8 q12 hap1 hq4Can hq8Can hq12Can
  have hlowCanSide : AspisR1.S9SideZeroTailRootV1.canonical low := hlowCan
  have hq16Side : AspisR1.S9SideZeroTailRootV1.qcanonical q16 := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q16)
    rw [generated_to_current_qm]
    exact hq16Can
  obtain ⟨output, htail, hcan0, hcan1, _⟩ :=
    AspisR1.S9SideZeroTailRootV1.sideZeroTail_total_exact
      weights0 low first3 all q16 hlowCanSide hfirst3Can hallCan hq16Side
  have hafter : @AspisR1S9TwoCallScalarMeaningV2.afterScalar
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 ap1 extra 0#usize
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
      AspisR1S9AfterScalarTermSumsV1.afterSums ap1 0#usize iterNext
        weights0 low first2 first3 all q4 q16) = _
    simp only [hwe,hwe1,hadd2,hwe2,hadd3,hwe3,haddAll,bind_tc_ok]
    unfold AspisR1S9AfterScalarTermSumsV1.afterSums
    simp only [if_true]
    have htailCont : (do
        let out ← AspisR1.S9SideZeroTailRootV1.sideZeroTail
          weights0 low first3 all q16
        ok (ControlFlow.cont (iterNext, out))) =
          (Result.ok (ControlFlow.cont (iterNext,output)) : Result Flow) := by
      rw [htail]
      rfl
    simp only [AspisR1.S9SideZeroTailRootV1.sideZeroTail, result_bind_assoc] at htailCont
    exact htailCont
  have hactive : @AspisR1S9FactoredLoopBodyShapeV3.activeBody
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps ap0 ap1 extra
      0#usize iterNext weights0 = .ok (ControlFlow.cont (iterNext,output)) := by
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
  exact ⟨output, hactive, hcan0, hcan1⟩

#print axioms from_fn_and_sums_total
#print axioms side_zero_active_body_total

end AspisR1S9SideZeroActiveBodyTotalityV1
