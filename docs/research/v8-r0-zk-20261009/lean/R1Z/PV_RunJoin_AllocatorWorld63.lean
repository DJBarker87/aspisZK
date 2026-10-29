import R1Z.PV_FXM_ReserveSelected
/-! Qualified V183 packet. The world is an argument of the dictionary family,
and each continuation receives the post-world. Public-size allocation failure
remains runtime/allocator adequacy under rdea-1; no success law is assumed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AllocatorWorld63
open Aeneas Aeneas.Std Result ProverRwFull
open PV_FXM_ReserveWorld
variable [ExternalTypes]

structure Runtime (S F : Type) where
  step : Request → S → Option Nat × S
  shape : Type → Shape
  metadata : World S F → {T : Type} → (v : alloc.vec.Vec T) → PV_FXM_ReserveSelected.Metadata v
  encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError

def selectedAt {S F : Type} (runtime : Runtime S F) (ops : ExternalFuns) (w : World S F) : ExternalFuns :=
  PV_FXM_ReserveSelected.selected ops runtime.step Usize.max (Usize.max/2)
    runtime.shape (runtime.metadata w) runtime.encode w

def execute {T S F : Type} (runtime : Runtime S F) (w : World S F)
    (v : alloc.vec.Vec T) (n : Usize) : Execution T S F :=
  native runtime.step Usize.max (Usize.max/2) (runtime.shape T)
    (PV_FXM_ReserveSelected.buffer v (runtime.metadata w v)) n.val w

theorem complete {T S F : Type} (runtime : Runtime S F) (ops : ExternalFuns)
    (w : World S F) (A : Type) (v : alloc.vec.Vec T) (n : Usize) :
    @alloc.vec.Vec.try_reserve_exact _ (selectedAt runtime ops w) T A v n =
      ok (PV_FXM_ReserveSelected.returned runtime.encode (execute runtime w v n).returned,v) :=
  PV_FXM_ReserveSelected.complete ops A runtime.step Usize.max (Usize.max/2)
    runtime.shape (runtime.metadata w) runtime.encode v n w

/-- One actual selected callback and its state continuation. This retains inner
allocation errors and the exact post-header/world even when allocation fails. -/
def resume {T S F A : Type} (runtime : Runtime S F) (ops : ExternalFuns)
    (w : World S F) (Allocator : Type) (v : alloc.vec.Vec T) (n : Usize)
    (caller : core.result.Result Unit alloc.collections.TryReserveError →
      alloc.vec.Vec T → World S F → Result A) : Result A := do
  let (r,v') ← @alloc.vec.Vec.try_reserve_exact _ (selectedAt runtime ops w) T Allocator v n
  caller r v' (execute runtime w v n).world

theorem execution {T S F A : Type} (runtime : Runtime S F) (ops : ExternalFuns)
    (w : World S F) (Allocator : Type) (v : alloc.vec.Vec T) (n : Usize)
    (caller : core.result.Result Unit alloc.collections.TryReserveError →
      alloc.vec.Vec T → World S F → Result A) :
    resume runtime ops w Allocator v n caller =
      caller (PV_FXM_ReserveSelected.returned runtime.encode
        (execute runtime w v n).returned) v (execute runtime w v n).world := by
  simp only [resume,complete,bind_tc_ok,Aeneas.Std.uncurry]

/-- Two consecutive requests select the second callback at the first call's
post-world, rather than silently resetting the allocator. -/
theorem sequential {T U S F A : Type} (runtime : Runtime S F) (ops : ExternalFuns)
    (w : World S F) (Allocator : Type) (v : alloc.vec.Vec T) (n : Usize)
    (u : alloc.vec.Vec U) (m : Usize)
    (caller : core.result.Result Unit alloc.collections.TryReserveError →
      core.result.Result Unit alloc.collections.TryReserveError → World S F → Result A) :
    resume runtime ops w Allocator v n (fun r _ w' =>
      resume runtime ops w' Allocator u m (fun s _ w'' => caller r s w'')) =
    let first := execute runtime w v n
    let second := execute runtime first.world u m
    caller (PV_FXM_ReserveSelected.returned runtime.encode first.returned)
      (PV_FXM_ReserveSelected.returned runtime.encode second.returned) second.world := by
  rw [execution,execution]

#print axioms Runtime
#print axioms selectedAt
#print axioms execute
#print axioms complete
#print axioms resume
#print axioms execution
#print axioms sequential
end R1Z.PV_RunJoin_AllocatorWorld63
