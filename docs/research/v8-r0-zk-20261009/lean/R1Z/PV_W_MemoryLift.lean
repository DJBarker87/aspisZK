import R1Z.PV_W_ReachedEffects
import R1Z.PV_FXM_DropSelected
import R1Z.PV_FXM_ReserveSelected
import R1Z.PV_FXM_ZeroConsumed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_MemoryLift
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes]
variable {W S F C A B : Type}

/-- The view/commit are interpreter DATA. Native association of the current
owned header and commit is a separate P obligation; it is not a T field. -/
def statePair (view : W → S) (commit : W → S → W) (step : S → A × S) :
    M W (Option C) Aeneas.Std.Error A := fun w =>
  let r := step (view w)
  ⟨.ok r.1,commit w r.2,[(w,none)]⟩

def StateStep (view : W → S) (commit : W → S → W) (step : S → A × S)
    (w : W) (tag : Option C) (next : W) : Prop :=
  tag = none ∧ next = commit w (step (view w)).2

theorem state_valid (view : W → S) (commit : W → S → W) (step : S → A × S) :
    Valid (StateStep (C := C) view commit step) (statePair view commit step) := by
  intro w
  exact .cons ⟨rfl,rfl⟩ (.nil _)

theorem state_bind (view : W → S) (commit : W → S → W) (step : S → A × S)
    (k : A → M W (Option C) Aeneas.Std.Error B) (w : W) :
    PV_W_Threading.bind (statePair view commit step) k w =
      let r := step (view w)
      let tail := k r.1 (commit w r.2)
      ⟨tail.outcome,tail.world,[(w,none)] ++ tail.calls⟩ := rfl

def dropWords (view : W → PV_FXM_DropWorld.World S F)
    (commit : W → PV_FXM_DropWorld.World S F → W)
    (free : Nat → Nat → Nat → S → S) (buffer : PV_FXM_DropWorld.Buffer) :
    M W (Option C) Aeneas.Std.Error Unit :=
  statePair view commit (PV_FXM_DropWorld.native free buffer)

theorem drop_source (ops : ExternalFuns) (v : alloc.vec.Vec U32)
    (view : W → PV_FXM_DropWorld.World S F)
    (commit : W → PV_FXM_DropWorld.World S F → W)
    (free : Nat → Nat → Nat → S → S) (buffer : PV_FXM_DropWorld.Buffer) (w : W) :
    (dropWords (C := C) view commit free buffer w).outcome =
      PV_W_SourceSyntax.resultOutcome
        (@core.mem.drop _ (PV_FXM_DropSelected.selected ops) _ v) := by
  rw [PV_FXM_DropSelected.installed]
  rfl

theorem drop_world (view : W → PV_FXM_DropWorld.World S F)
    (commit : W → PV_FXM_DropWorld.World S F → W)
    (free : Nat → Nat → Nat → S → S) (buffer : PV_FXM_DropWorld.Buffer) (w : W) :
    (dropWords (C := C) view commit free buffer w).world =
      commit w (PV_FXM_DropWorld.reference free buffer (view w)).2 := by
  change commit w (PV_FXM_DropWorld.native free buffer (view w)).2 = _
  rw [PV_FXM_DropWorld.source_reference]

/-- The post-buffer/header is supplied to commit, even though the extracted
Vec value projects only its elements. No old-capacity reconstruction occurs. -/
def reserve {T : Type} (view : W → PV_FXM_ReserveWorld.World S F)
    (commit : W → PV_FXM_ReserveWorld.Buffer T → PV_FXM_ReserveWorld.World S F → W)
    (step : PV_FXM_ReserveWorld.Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : PV_FXM_ReserveWorld.Shape)
    (v : alloc.vec.Vec T) (metadata : PV_FXM_ReserveSelected.Metadata v)
    (additional : Usize)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError) :
    M W (Option C) Aeneas.Std.Error
      ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T) := fun w =>
  let e := PV_FXM_ReserveWorld.native step wordMax byteMax shape
    (PV_FXM_ReserveSelected.buffer v metadata) additional.val (view w)
  ⟨.ok (PV_FXM_ReserveSelected.returned encode e.returned,v),
    commit w e.buffer e.world,[(w,none)]⟩

theorem reserve_source {T : Type} (ops : ExternalFuns) (Allocator : Type)
    (view : W → PV_FXM_ReserveWorld.World S F)
    (commit : W → PV_FXM_ReserveWorld.Buffer T → PV_FXM_ReserveWorld.World S F → W)
    (step : PV_FXM_ReserveWorld.Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Type → PV_FXM_ReserveWorld.Shape)
    (metadata : {U : Type} → (v : alloc.vec.Vec U) → PV_FXM_ReserveSelected.Metadata v)
    (v : alloc.vec.Vec T) (n : Usize)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError) (w : W) :
    (reserve (C := C) view commit step wordMax byteMax (shape T) v (metadata v) n encode w).outcome =
      PV_W_SourceSyntax.resultOutcome
        (@alloc.vec.Vec.try_reserve_exact _
          (PV_FXM_ReserveSelected.selected ops step wordMax byteMax shape metadata encode (view w))
          T Allocator v n) := by
  rw [PV_FXM_ReserveSelected.complete]
  rfl

theorem reserve_world {T : Type}
    (view : W → PV_FXM_ReserveWorld.World S F)
    (commit : W → PV_FXM_ReserveWorld.Buffer T → PV_FXM_ReserveWorld.World S F → W)
    (step : PV_FXM_ReserveWorld.Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : PV_FXM_ReserveWorld.Shape)
    (v : alloc.vec.Vec T) (metadata : PV_FXM_ReserveSelected.Metadata v) (n : Usize)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError) (w : W) :
    (reserve (C := C) view commit step wordMax byteMax shape v metadata n encode w).world =
      let e := PV_FXM_ReserveWorld.reference step wordMax byteMax shape
        (PV_FXM_ReserveSelected.buffer v metadata) n.val (view w)
      commit w e.buffer e.world := by
  unfold reserve
  rw [PV_FXM_ReserveWorld.source_reference]

/-- Exact emitted byte dictionary. Custom Zeroize implementations do not
enter this interpreter case. Volatile writes and fences remain in the world. -/
def zeroArray (view : W → PV_FXM_ZeroWorld.World F)
    (commit : W → PV_FXM_ZeroWorld.World F → W)
    (address : Nat) (N : Usize) : M W (Option C) Aeneas.Std.Error (Array U8 N) :=
  statePair view commit (fun w => (Array.repeat N 0#u8,PV_FXM_ZeroWorld.native address N.val w))

theorem zero_source (ops : ExternalFuns) (N : Usize) (a : Array U8 N)
    (view : W → PV_FXM_ZeroWorld.World F) (commit : W → PV_FXM_ZeroWorld.World F → W)
    (address : Nat) (w : W) :
    (zeroArray (C := C) view commit address N w).outcome =
      PV_W_SourceSyntax.resultOutcome
        ((@Array.Insts.ZeroizeZeroize _ (PV_FXM_ZeroSelected.selected ops) U8 N
          (@zeroize.Zeroize.Blanket _ (PV_FXM_ZeroSelected.selected ops) U8
            U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a) := by
  rw [PV_FXM_ZeroConsumed.emitted_array]
  rfl

theorem zero_world (view : W → PV_FXM_ZeroWorld.World F)
    (commit : W → PV_FXM_ZeroWorld.World F → W) (address : Nat) (N : Usize) (w : W) :
    (zeroArray (C := C) view commit address N w).world =
      commit w (PV_FXM_ZeroWorld.indexed address 0 N.val (view w)) := by
  change commit w (PV_FXM_ZeroWorld.native address N.val (view w)) = _
  exact PV_FXM_ZeroWorld.caller_composition address N.val (view w) (commit w)

#print axioms state_valid
#print axioms state_bind
#print axioms drop_source
#print axioms drop_world
#print axioms reserve_source
#print axioms reserve_world
#print axioms zero_source
#print axioms zero_world
end R1Z.PV_W_MemoryLift
