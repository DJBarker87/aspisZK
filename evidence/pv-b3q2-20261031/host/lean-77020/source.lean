import PV_B3Q_FormattingBranches
namespace PV_B3Q_RangeIndexSource
open Aeneas Aeneas.Std PV_B3P_Groups14227 core.ops.range
set_option autoImplicit false
/-- Deployed Range<usize>::index: checked_sub fails precisely if end<start;
the next branch checks end<=length, then the raw pointer offset/metadata
primitive realizes this same immutable slice. Pointer realization is V370. -/
def source {α : Type} (s : Slice α) (r : Range Usize) : Result (Slice α) :=
 if hstart : r.start.val ≤ r.end.val then
  if hend : r.end.val ≤ s.val.length then
   .ok ⟨s.val.slice r.start.val r.end.val,by
     have := s.val.slice_length_le r.start.val r.end.val
     scalar_tac⟩
  else .fail .panic
 else .fail .panic

theorem binding {α : Type} (s : Slice α) (r : Range Usize) :
 source s r = core.slice.index.SliceIndexRangeUsizeSlice.index r s := by
 unfold source core.slice.index.SliceIndexRangeUsizeSlice.index
 by_cases hs : r.start.val ≤ r.end.val
 · by_cases he : r.end.val ≤ s.val.length
   · have h : r.start ≤ r.end ∧ r.end ≤ s.length := ⟨hs,he⟩
     simp only [hs,he,dif_pos,h,if_true]
   · have h : ¬(r.start ≤ r.end ∧ r.end ≤ s.length) := by
       intro h
       exact he h.2
     simp only [hs,he,dif_pos,dif_neg,h,if_false]
 · have h : ¬(r.start ≤ r.end ∧ r.end ≤ s.length) := by
     intro h
     exact hs h.1
   simp only [hs,dif_neg,h,if_false]

/-- All four projected Poseidon groups select a nonempty four-element range.
This supplies the source panic branch exclusion, not merely result equality. -/
theorem projected_group_range (group : Nat) (guard : group < 4) :
 4*group < 4*group+4 ∧ 4*group+4 ≤ 16 := by omega

theorem all_range_link (α : Type) : PV_B3P_Link_std_dependency_closure14
 (fun _ : Unit => Slice α → Range Usize → Result (Slice α))
 (fun _ => @source α)
 (fun _ s r => core.slice.index.SliceIndexRangeUsizeSlice.index r s) := by
 intro _
 funext s r
 exact binding s r
#print axioms binding
#print axioms projected_group_range
#print axioms all_range_link
end PV_B3Q_RangeIndexSource
