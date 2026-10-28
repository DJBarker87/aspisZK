import R1Z.PV_W_MemoryLift
import R1Z.PV_FXM_AuditInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_MemoryCombined
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes]
variable {W S F D DF ZF C T : Type}

/-- All four projections use the SAME current-world scoped selector already
merged on the candidate. Current header metadata is explicit. The theorem
transports the source packages into the calculus, not into a deployed ABI. -/
theorem current_selector (ops : ExternalFuns)
    (step : PV_FXM_ReserveWorld.Request → S → Option Nat × S)
    (wordMax byteMax : Nat) (shape : Type → PV_FXM_ReserveWorld.Shape)
    (metadata : {U : Type} → (v : alloc.vec.Vec U) → PV_FXM_ReserveSelected.Metadata v)
    (encode : PV_FXM_ReserveWorld.Error → alloc.collections.TryReserveError)
    (reserveView : W → PV_FXM_ReserveWorld.World S F)
    (reserveCommit : W → PV_FXM_ReserveWorld.Buffer T → PV_FXM_ReserveWorld.World S F → W)
    (dropView : W → PV_FXM_DropWorld.World D DF)
    (dropCommit : W → PV_FXM_DropWorld.World D DF → W)
    (free : Nat → Nat → Nat → D → D) (buffer : PV_FXM_DropWorld.Buffer)
    (zeroView : W → PV_FXM_ZeroWorld.World ZF)
    (zeroCommit : W → PV_FXM_ZeroWorld.World ZF → W)
    (address : Nat) (level : alloc.vec.Vec U32) (Allocator : Type)
    (v : alloc.vec.Vec T) (n N : Usize) (a : Array U8 N) (byte : U8) (w : W) :
    let selected := PV_FXM_AuditInstall.selected ops step wordMax byteMax shape metadata encode (reserveView w)
    (PV_W_MemoryLift.dropWords (C := C) dropView dropCommit free buffer w).outcome =
      PV_W_SourceSyntax.resultOutcome (selected.op4 level) ∧
    (PV_W_MemoryLift.reserve (C := C) reserveView reserveCommit step wordMax byteMax
      (shape T) v (metadata v) n encode w).outcome =
      PV_W_SourceSyntax.resultOutcome (selected.op32 Allocator v n) ∧
    (PV_W_MemoryLift.zeroArray (C := C) zeroView zeroCommit address N w).outcome =
      PV_W_SourceSyntax.resultOutcome
        ((@Array.Insts.ZeroizeZeroize _ selected U8 N
          (@zeroize.Zeroize.Blanket _ selected U8 U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a) ∧
    (PV_W_MemoryLift.statePair (C := C) zeroView zeroCommit
      (fun z => (0#u8,PV_FXM_ZeroWorld.byte address z)) w).outcome =
      PV_W_SourceSyntax.resultOutcome
        ((@zeroize.Zeroize.Blanket _ selected U8 U8.Insts.ZeroizeDefaultIsZeroes).zeroize byte) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · rw [PV_FXM_AuditInstall.drop]
    rfl
  · rw [PV_FXM_AuditInstall.reserve]
    rfl
  · exact congrArg PV_W_SourceSyntax.resultOutcome
      (PV_FXM_AuditInstall.array ops step wordMax byteMax shape metadata encode (reserveView w) a).symm
  · exact congrArg PV_W_SourceSyntax.resultOutcome
      (PV_FXM_AuditInstall.scalar ops step wordMax byteMax shape metadata encode (reserveView w) byte).symm

#print axioms current_selector
end R1Z.PV_W_MemoryCombined
