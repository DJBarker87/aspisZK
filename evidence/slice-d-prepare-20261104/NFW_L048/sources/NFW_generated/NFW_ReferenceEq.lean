import NFW_ReferenceFuns
import NFW_TranscriptDomain
set_option autoImplicit false
namespace AspisR1.NFW_ReferenceEq
open Aeneas Aeneas.Std Result
/-- These are extracted scalar descriptors, not an independently assumed
whole-prepare output. Native source association is recorded separately. -/
theorem control (q c : Bool) : NFW_Reference.prepared_control_ref q c =
 ok (if q then (1#u8,6#u8,false) else if c then (2#u8,9#u8,true) else (0#u8,9#u8,true)) := by
 cases q <;> cases c <;> rfl

theorem row_domain (i row : U8) (width : U32) (nonzero : Bool)
 (call : NFW_Reference.prepared_row_ref i=ok (some (row,width,nonzero))) :
 (row.val,width.val)∈NFW_TranscriptDomain.calls := by
 unfold NFW_Reference.prepared_row_ref at call
 split at call <;> simp at call
 all_goals rcases call with ⟨rfl,rfl,rfl⟩; decide

theorem scratch : NFW_Reference.scratch_size_ref=ok 14759#usize := rfl

theorem tx1 (k : Usize) : NFW_Reference.tx1_split_ref k=ok (decide (k=10#usize)) := rfl

theorem tx2 (next : Usize) : NFW_Reference.tx2_split_ref next=ok (decide (next=10#usize)) := rfl
#print axioms control
#print axioms row_domain
#print axioms scratch
#print axioms tx1
#print axioms tx2
end AspisR1.NFW_ReferenceEq
