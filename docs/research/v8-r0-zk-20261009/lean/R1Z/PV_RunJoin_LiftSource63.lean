import R1Z.PV_RunJoin_LiftPayload63
import R1Z.PV_RunJoin_BackendMRows58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftSource63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_LiftRow63 PV_RunJoin_LiftPayload63

/-- Native inner lift of the first 1024 cells. Longer columns are allowed;
there is no assumption of an encoded image or of source success. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns) (lane : Usize)
    (hl : lane.val<26)
    (enough : 1024≤(PV_RunJoin_BackendMRows58.column columns lane.val).length)
    (out : alloc.vec.Vec Q) (room : out.length+1024≤Usize.max) :
    ∃ next, @host_semantic.lift_columns_loop0_loop0 (types base)
      (selected base heap box ops) columns lane out 0#usize=ok next ∧
      next.val=out.val ++ payload (PV_RunJoin_BackendMRows58.column columns lane.val) 0 1024 ∧
      next.length=out.length+1024 := by
  have source : Array.index_usize columns lane=ok (PV_RunJoin_BackendMRows58.column columns lane.val) := by
    rw [ProverCommitArrayIndex25.array_index_usize_ok columns lane hl]
    simp only [PV_RunJoin_BackendMRows58.column,Nat.mod_eq_of_lt hl]
  obtain ⟨next,hn,hv⟩ := PV_RunJoin_LiftPayload63.complete columns lane _ source 1024 0#usize
    enough (by rfl) out room
  refine ⟨next,?_,hv,?_⟩
  · rw [PV_RunJoin_LiftRow63.complete base heap box ops columns lane 1024 out 0#usize rfl]
    exact hn
  · change next.val.length=out.val.length+1024
    rw [hv,List.length_append,PV_RunJoin_LiftPayload63.length]

#print axioms complete
end R1Z.PV_RunJoin_LiftSource63
