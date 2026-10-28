import R1Z.PV_DL_DefaultSelected
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_DL_DefaultCallback
open ProverRwFull PV_DL_DefaultSelected PV_CBL_GenericArrayPower PV_CBL_LibraryShapes
set_option autoImplicit false
abbrev Limit (base : ExternalTypes) := (@typenum.uint.UInt (Types base) (@typenum.uint.UInt (Types base) (@typenum.uint.UInt (Types base) (@typenum.uint.UInt (Types base) (@typenum.uint.UInt (Types base) (@typenum.uint.UInt (Types base) (@typenum.uint.UInt (Types base) (@typenum.uint.UInt (Types base) (@typenum.uint.UInt (Types base) typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)

theorem callback (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {T K N O : Type} (dc : core.default.Default T)
    (bk : digest.core_api.BufferKindUser T K N (Storage U8 6))
    (less : typenum.type_operators.IsLess N (Limit base) O)
    (nz : typenum.marker_traits.NonZero O)
    (dn : core.default.Default N) (dk : core.default.Default K)
    (hs : bk.crypto_commonBlockSizeUserInst.generic_arrayArrayLengthSelf_BlockSizeU8Self_Clause0_ArrayTypeInst.typenummarker_traitsUnsignedInst.USIZE=ok 64#usize) :
    letI : ExternalTypes := Types base
    @ExternalFuns.op217 (Types base) (selected base ops) T K N (Storage U8 6) O dc bk less nz dn dk =
      PV_DL_DefaultBuffer.model dc.default := by
  change dispatch _ _ _=PV_DL_DefaultBuffer.model dc.default
  exact dispatch_source _ _ _ hs

#print axioms Limit
#print axioms callback
end R1Z.PV_DL_DefaultCallback
