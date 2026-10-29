import R1Z.PV_RDCD3_CB_OwnedMaskLinearsEq
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_V217ReverseTotal
open Aeneas Aeneas.Std Result PV_RDCD3_Total PV_RDCD3_ReverseRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
namespace S
abbrev finite := PV_RDCD3_CB_MaskLinearsFinite.finite
abbrev loop := PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears_loop
abbrev complete := PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears
end S

set_option backward.isDefEq.respectTransparency false in
theorem finite_total (point : Array Q 10#usize) (fuel : Nat) (e : Usize) (s w : Q)
    (rank : e.val=fuel) (bounded : e.val≤10) : Total (S.finite point fuel e s w) := by
  induction fuel generalizing e s w with
  | zero => exact ok_total (s,w)
  | succ fuel ih =>
    have index : (pred e).val<10 := by rw [pred_val];omega
    obtain ⟨q,hq⟩ := PV_RDCD3_ArrayRead.read point (pred e) index
    obtain ⟨s1,hs⟩ := PV_RDCD3_FieldTotal.q_add s q
    simp only [S.finite,PV_RDCD3_CB_MaskLinearsFinite.finite,hq,hs,bind_tc_ok]
    have next_rank : (pred e).val=fuel := by rw [pred_val];omega
    have next_bound : (pred e).val≤10 := by omega
    split
    · apply bind_total (PV_RDCD3_FieldTotal.q_add w s1)
      intro w1
      exact ih (pred e) s1 w1 next_rank next_bound
    · exact ih (pred e) s1 w next_rank next_bound

set_option backward.isDefEq.respectTransparency false in
theorem source_total (point : Array Q 10#usize) (s w : Q) :
    Total (S.loop (before 10#usize) point s w) := by
  apply (congrArg PV_RDCD3_Total.Total (PV_RDCD3_CB_MaskLinearsFinite.source point 10 10#usize s w rfl)).mpr
  exact finite_total point 10 10#usize s w rfl (by decide)

set_option backward.isDefEq.respectTransparency false in
theorem complete (point : Array Q 10#usize) : Total (S.complete point) := by
  unfold S.complete PV_RDCD3_CB_MaskSource.state_only_hiding.selected_mask_linears
  simp only [core.iter.traits.iterator.Iterator.rev.default,
    core.iter.traits.iterator.Iterator.rev.trait_default,bind_tc_ok,
    PV_RDCD3_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS]
  apply bind_total (source_total point _ _)
  rintro ⟨s,w⟩
  apply bind_total (PV_RDCD3_FieldTotal.q_scale s _);intro a
  apply bind_total (PV_RDCD3_FieldTotal.q_scale w _);intro b
  apply bind_total (PV_RDCD3_FieldTotal.q_add a b);intro c
  apply bind_total (PV_RDCD3_FieldTotal.q_scale s _);intro d
  apply bind_total (PV_RDCD3_FieldTotal.q_scale w _);intro e
  apply bind_total (PV_RDCD3_FieldTotal.q_add d e);intro f
  exact ok_total (c,f)
#print axioms finite_total
#print axioms source_total
#print axioms complete
end R1Z.PV_RDCD3_V217ReverseTotal
