import R1Z.PV_RDCD_ZeroConsumed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD_ZeroDrop
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- The source Zeroizing::drop delegates to Z::zeroize exactly once. The
subsequent [u8;N] field glue has no user destructor or allocator action.
The owned value is consumed; only Unit and the write world are returned. -/
def dropArray {F : Type} (ops : ExternalFuns) (N : Usize) (a : Array U8 N)
    (address : Nat) (w : PV_RDCD_ZeroWorld.World F) :
    Result (Unit × PV_RDCD_ZeroWorld.World F) := do
  let _ ← (@Array.Insts.ZeroizeZeroize _ (PV_RDCD_ZeroSelected.selected ops) U8 N
    (@zeroize.Zeroize.Blanket _ (PV_RDCD_ZeroSelected.selected ops) U8
      U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a
  .ok ((),PV_RDCD_ZeroWorld.native address N.val w)

theorem complete {F : Type} (ops : ExternalFuns) (N : Usize) (a : Array U8 N)
    (address : Nat) (w : PV_RDCD_ZeroWorld.World F) :
    dropArray ops N a address w=.ok ((),PV_RDCD_ZeroWorld.indexed address 0 N.val w) := by
  change (do let _ ← PV_RDCD_ZeroSelected.array PV_RDCD_ZeroSelected.byteZero a
             Result.ok ((),PV_RDCD_ZeroWorld.native address N.val w)) = _
  simp only [PV_RDCD_ZeroSelected.array_value,bind_tc_ok]
  exact congrArg (fun q => Result.ok ((),q))
    (PV_RDCD_ZeroWorld.caller_composition address N.val w id)

theorem caller_composition {F A : Type} (ops : ExternalFuns) (N : Usize)
    (a : Array U8 N) (address : Nat) (w : PV_RDCD_ZeroWorld.World F)
    (caller : Unit → PV_RDCD_ZeroWorld.World F → Result A) :
    (do let (u,w') ← dropArray ops N a address w
        caller u w')=caller () (PV_RDCD_ZeroWorld.indexed address 0 N.val w) := by
  rw [complete]
  rfl

#print axioms complete
#print axioms caller_composition
end R1Z.PV_RDCD_ZeroDrop
