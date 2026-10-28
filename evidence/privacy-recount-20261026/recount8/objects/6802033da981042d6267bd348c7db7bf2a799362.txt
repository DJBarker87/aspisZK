import R1Z.PV_W_ReachedThreading
import R1Z.PV_W_MemoryLift
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RuntimeMemory38
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes]

/-- Live process/header associations, kept as runtime data. Associating these
views with deployed native memory remains P, never an entropy trust item. -/
structure Memory (W S F D DF ZF : Type) where
  reserveView : W → PV_FXM_ReserveWorld.World S F
  reserveCommit : {T : Type} → W → PV_FXM_ReserveWorld.Buffer T → PV_FXM_ReserveWorld.World S F → W
  allocate : PV_FXM_ReserveWorld.Request → S → Option Nat × S
  wordMax : Nat
  byteMax : Nat
  shape : Type → PV_FXM_ReserveWorld.Shape
  metadata : {T : Type} → W → (v : alloc.vec.Vec T) → PV_FXM_ReserveSelected.Metadata v
  encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError
  dropView : W → PV_FXM_DropWorld.World D DF
  dropCommit : W → PV_FXM_DropWorld.World D DF → W
  free : Nat → Nat → Nat → D → D
  dropBuffer : W → alloc.vec.Vec U32 → PV_FXM_DropWorld.Buffer
  zeroView : W → PV_FXM_ZeroWorld.World ZF
  zeroCommit : W → PV_FXM_ZeroWorld.World ZF → W
  arrayAddress : {N : Usize} → W → Array U8 N → Nat
  byteAddress : W → U8 → Nat

variable {W S F D DF ZF C : Type}

def algebra (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : Memory W S F D DF ZF) : PV_W_ReachedThreading.Algebra W (Option C) where
  base := base
  reserve := fun {T} _ v n w =>
    PV_W_MemoryLift.reserve memory.reserveView memory.reserveCommit memory.allocate
      memory.wordMax memory.byteMax (memory.shape T) v (memory.metadata w v) n memory.encode w
  dropWords := fun v w => PV_W_MemoryLift.dropWords memory.dropView memory.dropCommit
    memory.free (memory.dropBuffer w v) w
  zeroArray := fun N v w => PV_W_MemoryLift.zeroArray memory.zeroView memory.zeroCommit
    (memory.arrayAddress w v) N w
  zeroByte := fun v w => PV_W_MemoryLift.statePair memory.zeroView memory.zeroCommit
    (fun z => (0#u8,PV_FXM_ZeroWorld.byte (memory.byteAddress w v) z)) w

/-- Each reservation consults metadata in its current pre-world, rather than
capturing the initialization world's capacity. Its post-header is committed. -/
theorem reserve (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : Memory W S F D DF ZF) {T : Type} (Allocator : Type)
    (v : alloc.vec.Vec T) (n : Usize) (w : W) :
    ((algebra base memory).reserve Allocator v n w).world =
      let e := PV_FXM_ReserveWorld.reference memory.allocate memory.wordMax memory.byteMax
        (memory.shape T) (PV_FXM_ReserveSelected.buffer v (memory.metadata w v)) n.val (memory.reserveView w)
      memory.reserveCommit w e.buffer e.world :=
  PV_W_MemoryLift.reserve_world memory.reserveView memory.reserveCommit memory.allocate
    memory.wordMax memory.byteMax (memory.shape T) v (memory.metadata w v) n memory.encode w

/-- Reached allocation, drop and volatile-zero effects retain their own
pre-world call, including inner allocation errors. No OS-silence or native
purity is inferred from the `none` tag. -/
theorem reserve_trace (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : Memory W S F D DF ZF) {T : Type} (Allocator : Type)
    (v : alloc.vec.Vec T) (n : Usize) (w : W) :
    ((algebra base memory).reserve Allocator v n w).calls=[(w,none)] := rfl

theorem drop_trace (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : Memory W S F D DF ZF) (v : alloc.vec.Vec U32) (w : W) :
    ((algebra base memory).dropWords v w).calls=[(w,none)] := rfl

theorem zero_trace (base : PV_W_TypedEffects.Algebra W (Option C) Aeneas.Std.Error)
    (memory : Memory W S F D DF ZF) (N : Usize) (v : Array U8 N) (w : W) :
    ((algebra base memory).zeroArray N v w).calls=[(w,none)] := rfl

#print axioms reserve
#print axioms reserve_trace
#print axioms drop_trace
#print axioms zero_trace
end R1Z.PV_RunJoin_RuntimeMemory38
