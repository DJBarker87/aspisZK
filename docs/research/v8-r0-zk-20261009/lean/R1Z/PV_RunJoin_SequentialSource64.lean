import R1Z.PV_RunJoin_Sequential64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SequentialSource64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_Sequential64
variable [ExternalTypes] [ExternalFuns]

theorem reserve {A T S F Allocator : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S F)
    (ops : ExternalFuns) (w : PV_FXM_ReserveWorld.World S F)
    (v : alloc.vec.Vec T) (n : Usize)
    (next : core.result.Result Unit alloc.collections.TryReserveError → alloc.vec.Vec T → Plan A) :
    execute runtime (.reserve v n next) w=
      PV_RunJoin_AllocatorWorld63.resume runtime ops w Allocator v n
        (fun r v' w' => execute runtime (next r v') w') := by
  rw [PV_RunJoin_AllocatorWorld63.execution]
  rfl

/-- This is the sequential residual condition: the second invocation is on the
closure/count computed from the FIRST actual returned vector, not a separately
chosen successful input. This theorem is a scheduling tool, not native P. -/
theorem workers {A T U G H S F : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S F)
    (w : PV_FXM_ReserveWorld.World S F)
    (firstInst : core.ops.function.Fn G Usize T) (cost count : Usize) (f : G)
    (secondInst : alloc.vec.Vec T → core.ops.function.Fn H Usize U)
    (secondCost secondCount : alloc.vec.Vec T → Usize) (secondClosure : alloc.vec.Vec T → H)
    (tail : alloc.vec.Vec T → alloc.vec.Vec U → Plan A)
    (success : ∃ first, host_work.map firstInst cost count f=ok first ∧
      ∃ second, host_work.map (secondInst first) (secondCost first) (secondCount first)
        (secondClosure first)=ok second ∧ Success runtime (tail first second) w) :
    ∃ a w', execute runtime (.worker firstInst cost count f (fun first =>
      .worker (secondInst first) (secondCost first) (secondCount first) (secondClosure first)
        (tail first))) w=ok (a,w') := by
  obtain ⟨first,hfirst,second,hsecond,htail⟩ := success
  apply sound
  exact Success.worker firstInst cost count f _ w first hfirst
    (Success.worker (secondInst first) (secondCost first) (secondCount first)
      (secondClosure first) _ w second hsecond htail)

#print axioms reserve
#print axioms workers
end R1Z.PV_RunJoin_SequentialSource64
