import R1Z.PV_RDB2_DL_DefaultBuffer
import R1Z.PV_RDB2_CBL_LibraryShapeTypes
import R1Z.PV_RDB2_FullExternalFuns
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_DL_DefaultSelected
open ProverRwFull PV_CBL_GenericArrayPower PV_CBL_LibraryShapes
set_option autoImplicit false
abbrev Types := PV_CBL_LibraryShapeTypes.selectedTypes

def dispatch {T A : Type} (size : Result Usize) (core : Result T)
    (fallback : Unit → Result (Wrapper T A)) : Result (Wrapper T A) := by
  classical
  by_cases hA : A=Storage U8 6
  · subst A
    exact if size=ok 64#usize then PV_DL_DefaultBuffer.model core else fallback ()
  · exact fallback ()

theorem dispatch_source {T : Type} (size : Result Usize) (core : Result T)
    (fallback : Unit → Result (Wrapper T (Storage U8 6))) (hs : size=ok 64#usize) :
    dispatch size core fallback=PV_DL_DefaultBuffer.model core := by
  classical
  simp only [dispatch,hs,if_true]
  exact dif_pos True.intro

/-- A selected 64-byte storage candidate. Native row closure is reported
separately; this dictionary equation alone is not source correspondence. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with
    op217 := fun dc bk less nz dn dk =>
      dispatch
        bk.crypto_commonBlockSizeUserInst.generic_arrayArrayLengthSelf_BlockSizeU8Self_Clause0_ArrayTypeInst.typenummarker_traitsUnsignedInst.USIZE
        dc.default (fun _ => ops.op217 dc bk less nz dn dk)}

#print axioms dispatch
#print axioms dispatch_source
#print axioms selected
end R1Z.PV_DL_DefaultSelected
