import S9CandidateActiveBodyAssemblerV1
import S9SideZeroTailRootV1
import S9SideOneTailTotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9P6AfterTermsTotalV1
open AspisR1S9HelperP6
local instance selectedOps : FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
abbrev U := Std.Usize
abbrev S := field.WideExact
abbrev Q := field.QM31
abbrev W := Array S (4#usize)
abbrev R := core.ops.range.Range U
abbrev Flow := ControlFlow (R × W) W
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev CanonicalQ (q : Q) := AspisR1CurrentWide.Proof.CanonicalQM
  (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q)
abbrev cells (a : W) (j : Fin 4) := AspisR1.S9ArrayWriteScheduleRootV1.cells a j

private theorem result_bind_assoc {A B C : Type}
    (m : Result A) (k : A → Result B) (h : B → Result C) :
    (do let b ← (do let a ← m; k a); h b) =
      (do let a ← m; let b ← k a; h b) := by
  cases m <;> rfl

private theorem index_exists (a : W) (i : U) (hi : i.val < 4) :
    ∃ x, Array.index_usize a i = .ok x := by
  obtain ⟨x,hx,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec a i (by simpa [a.property] using hi))
  exact ⟨x,hx⟩

private theorem qm_carrier (q : Q) :
    AspisR1S9GeneratedWideMulQM31V2.toQM q =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q := by
  cases q; rfl

/-- Constructs the exact continuation from canonical reads, retaining its
same term array. The nonzero branch needs canonical old[1]; both branches
return canonical cell1 for the following source step. -/
theorem p6_after_terms_total
    (ap1 terms : W) (side : U) (iterNext : R) (old : W)
    (low : S) (q4 q16 : Q)
    (hap1 : ∀ j x, Array.index_usize ap1 j = .ok x → Canonical x)
    (hterms : ∀ j x, Array.index_usize terms j = .ok x → Canonical x)
    (hlow : Canonical low) (hq4 : CanonicalQ q4) (hq16 : CanonicalQ q16)
    (hold : side ≠ 0#usize → ∀ x,
      Array.index_usize old 1#usize = .ok x → Canonical x) :
    ∃ out, @AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms selectedOps
      ap1 terms side iterNext old low q4 q16 = .ok (.cont (iterNext,out)) ∧
      Canonical (cells out 1) := by
  obtain ⟨t0,h0⟩ := index_exists terms 0#usize (by decide)
  obtain ⟨t1,h1⟩ := index_exists terms 1#usize (by decide)
  obtain ⟨t2,h2⟩ := index_exists terms 2#usize (by decide)
  obtain ⟨t3,h3⟩ := index_exists terms 3#usize (by decide)
  obtain ⟨first2,ha2,hc2,_⟩ := AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact
    t0 t1 (hterms _ _ h0) (hterms _ _ h1)
  obtain ⟨first3,ha3,hc3,_⟩ := AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact
    first2 t2 hc2 (hterms _ _ h2)
  obtain ⟨all,haAll,hcAll,_⟩ := AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact
    first3 t3 hc3 (hterms _ _ h3)
  have h16 : AspisR1.S9SideZeroTailRootV1.qcanonical q16 := by
    change AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q16)
    rw [qm_carrier]; exact hq16
  by_cases hs : side = 0#usize
  · obtain ⟨out,htail,_hc0,hc1,_⟩ :=
      AspisR1.S9SideZeroTailRootV1.sideZeroTail_total_exact
        old low first3 all q16 hlow hc3 hcAll h16
    refine ⟨out,?_,hc1⟩
    unfold AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
    simp only [field.WideExact.add,
      AspisR1S9ConcreteFieldOpsV1.concrete_wideAdd_dispatch,
      AspisR1S9ConcreteFieldOpsV1.actualWideAdd,
      h0,h1,h2,h3,ha2,ha3,haAll,bind_tc_ok,if_pos hs]
    have ht : (do
        let out ← AspisR1.S9SideZeroTailRootV1.sideZeroTail old low first3 all q16
        ok (.cont (iterNext,out))) = (Result.ok (.cont (iterNext,out)) : Result Flow) := by
      rw [htail]; rfl
    simp only [AspisR1.S9SideZeroTailRootV1.sideZeroTail,result_bind_assoc] at ht
    exact ht
  · obtain ⟨out,htail,hc1,_hc2,_hc3⟩ :=
      AspisR1.S9SideOneTailTotalV1.side_one_tail_total old ap1 low all first2 q4 q16
        hlow hcAll hc2 hq4 hq16 (hold hs) hap1
    refine ⟨out,?_,hc1⟩
    unfold AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
    simp only [field.WideExact.add,
      AspisR1S9ConcreteFieldOpsV1.concrete_wideAdd_dispatch,
      AspisR1S9ConcreteFieldOpsV1.actualWideAdd,
      h0,h1,h2,h3,ha2,ha3,haAll,bind_tc_ok,if_neg hs]
    have ht : (do
        let out ← AspisR1.S9SideOneTailRootV1.sideOneTail old ap1 low all first2 q4 q16
        ok (.cont (iterNext,out))) = (Result.ok (.cont (iterNext,out)) : Result Flow) := by
      rw [htail]; rfl
    simp only [AspisR1.S9SideOneTailRootV1.sideOneTail,result_bind_assoc] at ht
    exact ht

#print axioms p6_after_terms_total
end AspisR1S9P6AfterTermsTotalV1
