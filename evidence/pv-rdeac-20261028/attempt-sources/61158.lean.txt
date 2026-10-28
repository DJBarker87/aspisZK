import R1Z.PV_CBL_ShaCore
import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ShaTypes
open ProverRwFull
set_option autoImplicit false
@[reducible] def selectedTypes (base : ExternalTypes) : ExternalTypes :=
  { base with op10 := PV_CBL_ShaCore.Core }
abbrev Blocks (base : ExternalTypes) : Type :=
  letI : ExternalTypes := base
  Slice (generic_array.GenericArray Std.U8
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt typenum.uint.UTerm
        typenum.bit.B1) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplOdd Std.U8 (Array Std.U8 0#usize)))))))))
theorem core_carrier (base : ExternalTypes) :
    @sha2.core_api.Sha256VarCore (selectedTypes base) = PV_CBL_ShaCore.Core := rfl

theorem blocks_carrier (base : ExternalTypes) :
    Blocks (selectedTypes base) = Blocks base := rfl
#print axioms core_carrier
#print axioms blocks_carrier
end R1Z.PV_CBL_ShaTypes
