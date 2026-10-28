import R1Z.PV_RDCD_ZeroConsumed
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_ZeroizingSelected
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
/-- Source Zeroizing::zeroize delegates to its field dictionary once. The
emitted transparent wrapper has carrier Z. Effects are retained separately. -/
def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_RDCD_ZeroSelected.selected ops with op130 := fun d z => d.zeroize z}

theorem byte_dictionary (ops : ExternalFuns) :
    @zeroize.Zeroize.Blanket _ (selected ops) U8 U8.Insts.ZeroizeDefaultIsZeroes =
      PV_RDCD_ZeroSelected.byteZero := rfl

theorem array (ops : ExternalFuns) (N : Usize) (v : Array U8 N) :
    (@Array.Insts.ZeroizeZeroize _ (selected ops) U8 N
      (@zeroize.Zeroize.Blanket _ (selected ops) U8 U8.Insts.ZeroizeDefaultIsZeroes)).zeroize v =
      .ok (Array.repeat N 0#u8) := PV_RDCD_ZeroSelected.array_value v

theorem wrapper (ops : ExternalFuns) (N : Usize) (v : zeroize.Zeroizing (Array U8 N)) :
    (selected ops).op130 (@Array.Insts.ZeroizeZeroize _ (selected ops) U8 N
      (@zeroize.Zeroize.Blanket _ (selected ops) U8 U8.Insts.ZeroizeDefaultIsZeroes)) v =
      .ok (Array.repeat N 0#u8) := array ops N v
#print axioms byte_dictionary
#print axioms array
#print axioms wrapper
end R1Z.PV_RJDec_ZeroizingSelected
