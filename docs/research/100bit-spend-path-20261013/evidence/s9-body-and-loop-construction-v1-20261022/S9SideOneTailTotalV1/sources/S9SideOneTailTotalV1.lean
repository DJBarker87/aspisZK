import S9SideOneTailRootV1
import S9SideOneMeaningRootV1
import S9ConcreteArithmeticAcceptedRootV1
import S9ConcreteQMMulAcceptedRootV1
import S9QMMulTotalCanonicalV1
import S9WideMulM31ReuseRootV2
import S3S9ConcreteFieldOpsV1
import S3S9TransparentFoldS2InstanceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1.S9SideOneTailTotalV1

open AspisR1S9HelperP6
local instance selectedOps : FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev S := field.WideExact
abbrev Q := field.QM31
abbrev A := Array S (4#usize)
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev CanonicalQ := AspisR1.S9ConcreteArithmeticAcceptedRootV1.CanonicalQ

private theorem helper_qm_eq_generated (q : Q) :
    AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q =
      AspisR1S9GeneratedWideMulQM31V2.toQM q := by
  cases q <;> rfl

private theorem index_success_exists {α : Type} (a : Array α (4#usize))
    (i : Usize) (hi : i.val < 4) : ∃ x, Array.index_usize a i = .ok x := by
  obtain ⟨x, hx, _⟩ := WP.spec_imp_exists
    (Array.index_usize_spec a i (by simpa [a.property] using hi))
  exact ⟨x, hx⟩

private theorem update_success_exists {α : Type} (a : Array α (4#usize))
    (i : Usize) (x : α) (hi : i.val < 4) :
    ∃ out, Array.update a i x = .ok out := by
  obtain ⟨out, hout, _⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by simpa [a.property] using hi))
  exact ⟨out, hout⟩

/-- The actual side-one source suffix is total from canonical reads and
canonical term inputs. The theorem constructs every intermediate result in
source order, then uses the retained successful-tail semantics to report the
canonical cells written by this exact output. -/
theorem side_one_tail_total
    (old ap1 : A) (low all first2 : S) (q4 q16 : Q)
    (hlow : Canonical low) (hall : Canonical all) (hfirst2 : Canonical first2)
    (hq4 : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q4))
    (hq16 : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q16))
    (hold : ∀ x, Array.index_usize old 1#usize = .ok x → Canonical x)
    (hap1 : ∀ i x, Array.index_usize ap1 i = .ok x → Canonical x) :
    ∃ out : A,
      AspisR1.S9SideOneTailRootV1.sideOneTail old ap1 low all first2 q4 q16 = .ok out ∧
      Canonical (AspisR1.S9ArrayWriteScheduleRootV1.cells out 1) ∧
      Canonical (AspisR1.S9ArrayWriteScheduleRootV1.cells out 2) ∧
      Canonical (AspisR1.S9ArrayWriteScheduleRootV1.cells out 3) := by
  obtain ⟨old1, hold1⟩ := index_success_exists old 1#usize (by decide)
  have hcanOld1 := hold old1 hold1
  obtain ⟨idx, hidx⟩ := index_success_exists weights.PERM 3#usize (by decide)
  have hperm3 := AspisR1S9TransparentFoldS2InstanceV1.perm_reads.2.2.2
  have hidxEq : idx = 1#usize := Result.ok.inj (hidx.symm.trans hperm3)
  have hidxbound : idx.val < 4 := by rw [hidxEq]; decide
  obtain ⟨ap1idx, hap1idx⟩ := index_success_exists ap1 idx hidxbound
  have hcanAp1 := hap1 idx ap1idx hap1idx
  have hq16g : CanonicalQ q16 := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q16)
    rw [← helper_qm_eq_generated]
    exact hq16
  obtain ⟨we6, hwe6, hcan6, _⟩ :=
    AspisR1.S9WideMulM31ReuseRootV2.concrete_wideMulM31_total_exact
      ap1idx weights.QUARTER hcanAp1
  obtain ⟨we7, hwe7, hcan7, _⟩ :=
    AspisR1S9ConcreteFieldOpsV1.actualWideMul_total_exact low we6 hlow hcan6
  obtain ⟨we8, hwe8, hcan8, _⟩ :=
    AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact old1 we7 hcanOld1 hcan7
  obtain ⟨weights1, hw1⟩ := update_success_exists old 1#usize we8 (by decide)
  obtain ⟨we9, hwe9, hcan9, _⟩ :=
    AspisR1S9ConcreteFieldOpsV1.actualWideMul_total_exact low all hlow hall
  have hq4g : CanonicalQ q4 := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q4)
    rw [← helper_qm_eq_generated]
    exact hq4
  obtain ⟨we10, hwe10, hcan10, _⟩ :=
    AspisR1S9ConcreteWideMulQM31ScalarProductV1.concrete_wideMulQM31_total_scalar_product
      we9 q4 hcan9 hq4g
  obtain ⟨weights2, hw2⟩ := update_success_exists weights1 2#usize we10 (by decide)
  obtain ⟨we11, hwe11, hcan11, _⟩ :=
    AspisR1S9ConcreteFieldOpsV1.actualWideMul_total_exact low first2 hlow hfirst2
  obtain ⟨q3, hq3, hcanQ3⟩ :=
    AspisR1S9QMMulTotalCanonicalV1.concrete_qm_mul_total q16 q4 hq16 hq4
  have hq3g : CanonicalQ q3 := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q3)
    rw [← helper_qm_eq_generated]
    exact hcanQ3
  obtain ⟨we12, hwe12, hcan12, _⟩ :=
    AspisR1S9ConcreteWideMulQM31ScalarProductV1.concrete_wideMulQM31_total_scalar_product
      we11 q3 hcan11 hq3g
  obtain ⟨out, hout⟩ := update_success_exists weights2 3#usize we12 (by decide)
  have hrun : AspisR1.S9SideOneTailRootV1.sideOneTail
      old ap1 low all first2 q4 q16 = .ok out := by
    unfold AspisR1.S9SideOneTailRootV1.sideOneTail
    simp only [
      AspisR1S9HelperP6.field.WideExact.mul_m31,
      AspisR1S9HelperP6.field.WideExact.mul,
      AspisR1S9HelperP6.field.WideExact.add,
      AspisR1S9HelperP6.field.WideExact.mul_qm31,
      AspisR1S9HelperP6.field.QM31.mul,
      hold1, hidx, hap1idx,
      AspisR1S9ConcreteFieldOpsV1.concrete_wideMul_dispatch,
      AspisR1S9ConcreteFieldOpsV1.concrete_wideAdd_dispatch,
      AspisR1S9ConcreteFieldOpsV1.actualWideAdd,
      hwe6, hwe7, hwe8, hw1, hwe9, hwe10, hw2, hwe11, hq3, hwe12, hout,
      bind_tc_ok]
  obtain ⟨_permIndex, _last, _hperm, _hlast, hc1, hc2, hc3, _hformula⟩ :=
    AspisR1.S9SideOneMeaningRootV1.sideOneTail_success_exact
      old ap1 low all first2 q4 q16 out hlow hall hfirst2 hq4g hq16g hold hap1 hrun
  exact ⟨out, hrun, hc1, hc2, hc3⟩

#print axioms side_one_tail_total

end AspisR1.S9SideOneTailTotalV1
