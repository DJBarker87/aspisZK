import R1Z.ProverRwFullFuns
import R1Z.PV_FXM_ZeroSelected
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_FXM_ZeroConsumed
open Aeneas Aeneas.Std ProverRwFull PV_FXM_ZeroSelected
variable [ExternalTypes]

/-- Exact emitted primitive marker dictionary, not an invented witness. -/
theorem emitted_default : U8.Insts.ZeroizeDefaultIsZeroes=byteDefault := rfl

theorem emitted_scalar (ops : ExternalFuns) :
    @zeroize.Zeroize.Blanket _ (selected ops) U8
      U8.Insts.ZeroizeDefaultIsZeroes = byteZero := rfl

theorem emitted_array (ops : ExternalFuns) (N : Usize) (a : Array U8 N) :
    (@Array.Insts.ZeroizeZeroize _ (selected ops) U8 N
      (@zeroize.Zeroize.Blanket _ (selected ops) U8
        U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a =
      .ok (Array.repeat N 0#u8) := array_value a

theorem emitted_execution {F A : Type} (ops : ExternalFuns)
    (N : Usize) (a : Array U8 N) (address : Nat)
    (w : PV_FXM_ZeroWorld.World F)
    (caller : Array U8 N → PV_FXM_ZeroWorld.World F → Result A) :
    (do let a' ← (@Array.Insts.ZeroizeZeroize _ (selected ops) U8 N
          (@zeroize.Zeroize.Blanket _ (selected ops) U8
            U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a
        caller a' (PV_FXM_ZeroWorld.native address N.val w)) =
      caller (Array.repeat N 0#u8) (PV_FXM_ZeroWorld.indexed address 0 N.val w) :=
  execution ops a address w caller

#print axioms emitted_default
#print axioms emitted_scalar
#print axioms emitted_array
#print axioms emitted_execution
end R1Z.PV_FXM_ZeroConsumed
