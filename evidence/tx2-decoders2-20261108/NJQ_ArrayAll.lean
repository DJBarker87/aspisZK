import NJQ_Words
import NJQ_CheckpointTrace
set_option autoImplicit false
noncomputable section
namespace NJQ_ArrayAll
open Aeneas Aeneas.Std Result NJI_CheckpointLoop
attribute [local instance] Classical.propDecidable

theorem coordinates {A : Type} [Inhabited A] {n : Usize} (a : Array A n) (P : A → Prop) :
 (∀ j,j<n.val → P (NHY_ArrayExt.coord a j)) ↔ ∀ x∈a.val,P x := by
 constructor
 · intro all x member
   obtain ⟨j,hj,same⟩:=List.mem_iff_getElem.mp member
   have bound : j<n.val := by rw [←a.property];exact hj
   have h:=all j bound
   simpa only [NHY_ArrayExt.coord,List.getElem?_eq_getElem hj,Option.getD_some,same] using h
 · intro all j bound
   have hj : j<a.val.length := by rw [a.property];exact bound
   have h:=all _ (List.getElem_mem hj)
   simpa only [NHY_ArrayExt.coord,List.getElem?_eq_getElem hj,Option.getD_some] using h

def All (target : Words) : Prop := ∀ j,j<8 → NHY_ArrayExt.coord target j≤capacity

theorem all_iff (target : Words) :
 All target ↔ target.val.any (fun x=>decide (x>capacity))=false := by
 have h : All target ↔ ∀ x∈target.val,x≤capacity := coordinates target (fun x=>x≤capacity)
 apply h.trans
 simp only [List.any_eq_false,decide_eq_true_eq,not_lt]

def loop (target : Words) : core.result.Result Words NJQ_CheckpointTrace.F :=
 match (scan target.val).2 with | .invalid=>.Err .InvalidMasterState | .accepted=>.Ok target

theorem loop_value (target : Words) :
 loop target=if All target then .Ok target else .Err .InvalidMasterState := by
 unfold loop
 rw [NJI_CheckpointLoop.first_error]
 by_cases all : All target
 · rw [(all_iff target).mp all]
   simp only [Bool.false_eq_true,ite_false,if_pos all]
 · have bad : target.val.any (fun x=>decide (x>capacity))=true := by
    cases h : target.val.any (fun x=>decide (x>capacity)) with
    | false=>exact False.elim (all ((all_iff target).mpr h))
    | true=>rfl
   rw [bad]
   simp only [ite_true,if_neg all]

/-- Native one-step/induction result = the source-ordered first-error scan model.
No successful-loop premise; both Rust Results are preserved. -/
theorem native_result (target : Words) (out : core.result.Result Words NJQ_CheckpointTrace.F)
 (trace : NJQ_CheckpointTrace.Trace target 0 (Array.repeat 8#usize 0#u64) out) :
 out=loop target := by
 rw [loop_value]
 exact NJQ_CheckpointTrace.initial target out trace

#print axioms coordinates
#print axioms all_iff
#print axioms loop_value
#print axioms native_result
end NJQ_ArrayAll
