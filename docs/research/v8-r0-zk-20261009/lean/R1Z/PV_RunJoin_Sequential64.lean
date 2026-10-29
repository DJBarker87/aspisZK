import R1Z.PV_RunJoin_NativeActual63
/-! Finite sequential success, with actual dependent continuations. This is a
proof tool for reifying the capture, not a claim that capture has been reified.
In particular there is no assumed equality between a plan and NativeControl.run.
Allocator failure is retained in execute and ruled out only by a named success
constructor, at the reached request/world. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Sequential64
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
open PV_FXM_ReserveWorld
abbrev Q := aspis_core.field.QM31

inductive Plan (A : Type) : Type 1 where
  | done : A → Plan A
  | step {B : Type} : Result B → (B → Plan A) → Plan A
  | terminal : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
      Array (Array Q 29#usize) 3#usize → Array Q 10#usize →
      aspis_core.state_only_prefix.r0.Challenges →
      (core.result.Result Q aspis_core.state_only_prefix.r0.Error → Plan A) → Plan A
  | worker {T F : Type} : core.ops.function.Fn F Usize T → Usize → Usize → F →
      (alloc.vec.Vec T → Plan A) → Plan A
  | reserve {T : Type} : alloc.vec.Vec T → Usize →
      (core.result.Result Unit alloc.collections.TryReserveError → alloc.vec.Vec T → Plan A) → Plan A

def execute {A S F : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S F) :
    Plan A → World S F → Result (A × World S F)
  | .done a,w => ok (a,w)
  | .step r next,w => do let b ← r;execute runtime (next b) w
  | .terminal public1 points alpha challenges next,w => do
      let r ← aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
        public1 points alpha challenges
      execute runtime (next r) w
  | .worker inst cost count f next,w => do
      let values ← host_work.map inst cost count f
      execute runtime (next values) w
  | .reserve v n next,w =>
      let event := PV_RunJoin_AllocatorWorld63.execute runtime w v n
      execute runtime (next (PV_FXM_ReserveSelected.returned runtime.encode event.returned) v) event.world

/-- Only reached inputs and continuations occur. The second worker may depend
on the first worker's returned vector; reserve advances to the exact post-world.
There are no unrelated arbitrary-input existentials. -/
inductive Success {A S F : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S F) :
    Plan A → World S F → Prop where
  | done (a : A) (w : World S F) : Success runtime (.done a) w
  | step {B : Type} (r : Result B) (next : B → Plan A) (w : World S F)
      (b : B) : r=ok b → Success runtime (next b) w → Success runtime (.step r next) w
  | terminal (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
      (points : Array (Array Q 29#usize) 3#usize) (alpha : Array Q 10#usize)
      (challenges : aspis_core.state_only_prefix.r0.Challenges)
      (next : core.result.Result Q aspis_core.state_only_prefix.r0.Error → Plan A) (w : World S F) (q : Q) :
      aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
        public1 points alpha challenges=ok (.Ok q) →
      Success runtime (next (.Ok q)) w → Success runtime (.terminal public1 points alpha challenges next) w
  | worker {T G : Type} (inst : core.ops.function.Fn G Usize T)
      (cost count : Usize) (f : G) (next : alloc.vec.Vec T → Plan A)
      (w : World S F) (values : alloc.vec.Vec T) :
      host_work.map inst cost count f=ok values → Success runtime (next values) w →
      Success runtime (.worker inst cost count f next) w
  | reserve {T : Type} (v : alloc.vec.Vec T) (n : Usize)
      (next : core.result.Result Unit alloc.collections.TryReserveError → alloc.vec.Vec T → Plan A)
      (w : World S F) :
      PV_FXM_ReserveSelected.returned runtime.encode
        (PV_RunJoin_AllocatorWorld63.execute runtime w v n).returned=.Ok () →
      Success runtime (next (.Ok ()) v) (PV_RunJoin_AllocatorWorld63.execute runtime w v n).world →
      Success runtime (.reserve v n next) w

theorem sound {A S F : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S F)
    (plan : Plan A) (w : World S F) (success : Success runtime plan w) :
    ∃ a w', execute runtime plan w=ok (a,w') := by
  induction success with
  | done a w => exact ⟨a,w,rfl⟩
  | step r next w b hr hs ih => simpa only [execute,hr,bind_tc_ok] using ih
  | terminal public1 points alpha challenges next w q hr hs ih =>
      simpa only [execute,hr,bind_tc_ok] using ih
  | worker inst cost count f next w values hr hs ih =>
      simpa only [execute,hr,bind_tc_ok] using ih
  | reserve v n next w hr hs ih => simpa only [execute,hr] using ih

#print axioms Plan
#print axioms execute
#print axioms Success
#print axioms sound
end R1Z.PV_RunJoin_Sequential64
