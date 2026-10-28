import R1Z.PV_W_MemoryLift
import R1Z.PV_FXM_ZeroDrop
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_ZeroizingBridge
open Aeneas Aeneas.Std ProverRwFull PV_W_Threading
variable [ExternalTypes]

/-- Source-value selector for the op130 wrapper body already recorded in
PV_CB_Op130Source. This definition retains all other fields of the scoped
byte selector. It is not an assertion about the complete deployed dictionary. -/
def wrapper (ops : ExternalFuns) : ExternalFuns :=
  {PV_FXM_ZeroSelected.selected ops with op130 := fun inst x => inst.zeroize x}

theorem wrapper_value (ops : ExternalFuns) (N : Usize) (a : Array U8 N) :
    @zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize _ (wrapper ops) _
      (@Array.Insts.ZeroizeZeroize _ (wrapper ops) U8 N
        (@zeroize.Zeroize.Blanket _ (wrapper ops) U8 U8.Insts.ZeroizeDefaultIsZeroes)) a =
      .ok (Array.repeat N 0#u8) := by
  change PV_FXM_ZeroSelected.array PV_FXM_ZeroSelected.byteZero a = _
  exact PV_FXM_ZeroSelected.array_value a

variable {W F C : Type}

theorem wrapper_outcome (ops : ExternalFuns) (N : Usize) (a : Array U8 N)
    (view : W → PV_FXM_ZeroWorld.World F) (commit : W → PV_FXM_ZeroWorld.World F → W)
    (address : Nat) (w : W) :
    (PV_W_MemoryLift.zeroArray (C := C) view commit address N w).outcome =
      PV_W_SourceSyntax.resultOutcome
        (@zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize _ (wrapper ops) _
          (@Array.Insts.ZeroizeZeroize _ (wrapper ops) U8 N
            (@zeroize.Zeroize.Blanket _ (wrapper ops) U8 U8.Insts.ZeroizeDefaultIsZeroes)) a) := by
  rw [wrapper_value]
  rfl

/-- Explicit zeroize and subsequent implicit Drop are two actions on native
live storage. They are not collapsed into one source-value overwrite. This
is a package-world count, not an L3 register/spill erasure theorem. -/
theorem explicit_then_drop_counts (address n : Nat) (w : PV_FXM_ZeroWorld.World F) :
    (PV_FXM_ZeroWorld.native address n (PV_FXM_ZeroWorld.native address n w)).writes =
      w.writes+n+n ∧
    (PV_FXM_ZeroWorld.native address n (PV_FXM_ZeroWorld.native address n w)).fences =
      w.fences+n+n := by
  obtain ⟨firstWrite,firstFence⟩ := PV_FXM_ZeroWorld.counts address n w
  obtain ⟨secondWrite,secondFence⟩ :=
    PV_FXM_ZeroWorld.counts address n (PV_FXM_ZeroWorld.native address n w)
  exact ⟨secondWrite.trans (congrArg (fun x => x+n) firstWrite),
    secondFence.trans (congrArg (fun x => x+n) firstFence)⟩

theorem drop_consumed_source (ops : ExternalFuns) (N : Usize) (a : Array U8 N)
    (address : Nat) (w : PV_FXM_ZeroWorld.World F) :
    PV_FXM_ZeroDrop.dropArray ops N a address w =
      .ok ((),PV_FXM_ZeroWorld.indexed address 0 N.val w) :=
  PV_FXM_ZeroDrop.complete ops N a address w

#print axioms wrapper_value
#print axioms wrapper_outcome
#print axioms explicit_then_drop_counts
#print axioms drop_consumed_source
end R1Z.PV_W_ZeroizingBridge
