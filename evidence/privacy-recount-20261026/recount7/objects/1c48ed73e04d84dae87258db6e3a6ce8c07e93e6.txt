import R1Z.PV_Src_PortInternalTotal
import R1Z.PV_Src_PortInternalField

/-! The unreduced source sum satisfies the exact bound needed by the
nonzero-lane field theorem. It is a consequence of the checked fold result. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalFullBound
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_Src_PortInternalStep PV_Src_PortInternalTotal

theorem part_bound (state : State) (part : U64)
    (hp : part.val = PV_Src_PortSumTotal.natSum ((tail state).val.map (UScalar.cast .U64))) :
    part.val < 68719476736 := by
  have hb := PV_Src_PortSumTotal.cast_bound (tail state).val
  have hl := tail_length state
  rw [← hp] at hb
  omega

theorem full_bound (state : State) (part : U64)
    (hp : part.val = PV_Src_PortSumTotal.natSum ((tail state).val.map (UScalar.cast .U64))) :
    (U64.wrapping_add part (UScalar.cast .U64 state.val[0]!)).val < 68719476736 := by
  have hb := PV_Src_PortSumTotal.cast_bound (tail state).val
  have hl := tail_length state
  rw [← hp] at hb
  have hx := u32lt state.val[0]!
  have he := add64v part (UScalar.cast .U64 state.val[0]!) part.val
    state.val[0]!.val rfl (c64 _) (by omega)
  rw [he]
  omega

#print axioms part_bound
#print axioms full_bound
end R1Z.PV_Src_PortInternalFullBound
