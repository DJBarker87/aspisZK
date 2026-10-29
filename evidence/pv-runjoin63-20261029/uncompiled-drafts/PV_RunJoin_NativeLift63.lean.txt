import R1Z.PV_RunJoin_LiftSource63
import R1Z.PV_RunJoin_LiftValue63
import R1Z.PV_RunJoin_NativeResidual63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeLift63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_LiftRow63 PV_RunJoin_LiftPayload63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (columns : Columns) (lane : Usize) (hl : lane.val<26)
    (enough : 1024≤(PV_RunJoin_BackendMRows58.column columns lane.val).length)
    (out : alloc.vec.Vec Q) (room : out.length+1024≤Usize.max) :
    ∃ next, @host_semantic.lift_columns_loop0_loop0 (types base)
      (opsNative base heap box ops runtime world) columns lane out 0#usize=ok next ∧
      next.val=out.val ++ payload (PV_RunJoin_BackendMRows58.column columns lane.val) 0 1024 ∧
      next.val.map PV_RunJoin_LiftValue63.value=out.val.map PV_RunJoin_LiftValue63.value ++
        PV_RunJoin_LiftValue63.widePayload (PV_RunJoin_BackendMRows58.column columns lane.val) 0 1024 ∧
      next.length=out.length+1024 := by
  obtain ⟨next,hn,hv,hlen⟩ := PV_RunJoin_LiftSource63.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world)
    columns lane hl enough out room
  refine ⟨next,hn,hv,?_,hlen⟩
  rw [hv,List.map_append,PV_RunJoin_LiftValue63.map_payload]

#print axioms complete
end R1Z.PV_RunJoin_NativeLift63
