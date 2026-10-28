import R1Z.PV_RDCD_ZeroConsumed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_WrapperValue
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
/-- Representation DATA. No native Zeroizing representation is asserted. -/
structure Representation (Z : Type) where
  view : zeroize.Zeroizing Z → Z
  replace : zeroize.Zeroizing Z → Z → zeroize.Zeroizing Z

def run {Z : Type} (repr : Representation Z) (d : zeroize.Zeroize Z)
    (v : zeroize.Zeroizing Z) : Result (zeroize.Zeroizing Z) := do
  let z ← d.zeroize (repr.view v)
  .ok (repr.replace v z)

theorem complete (ops : ExternalFuns) (N : Usize)
    (repr : Representation (Array U8 N)) (v : zeroize.Zeroizing (Array U8 N)) :
    run repr (@Array.Insts.ZeroizeZeroize _ (PV_RDCD_ZeroSelected.selected ops) U8 N
      (@zeroize.Zeroize.Blanket _ (PV_RDCD_ZeroSelected.selected ops) U8 U8.Insts.ZeroizeDefaultIsZeroes)) v =
      .ok (repr.replace v (Array.repeat N 0#u8)) := by
  unfold run
  rw [PV_RDCD_ZeroConsumed.emitted_array]
  rfl
#print axioms complete
end R1Z.PV_RJDec_WrapperValue
