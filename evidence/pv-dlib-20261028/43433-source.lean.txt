import R1Z.PV_DL_ShaSelected
import R1Z.PV_CBL_PaddingLength
open Aeneas Aeneas.Std Result ProverRwFull
noncomputable section
namespace R1Z.PV_DL_ShaRestoration
open PV_CBL_GenericArrayPower PV_CBL_LibraryShapes
set_option autoImplicit false

theorem position (pos : U8) : (UScalar.cast .Usize pos).val=pos.val := by
  rw [UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt (lt_of_lt_of_le pos.hBounds ?_)
  simp only [UScalarTy.U8_numBits_eq,UScalarTy.Usize_numBits_eq]
  exact Nat.pow_le_pow_right (by omega) (by cases System.Platform.numBits_eq <;> simp_all)

def suffix (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6)) : List U8 :=
  (PV_DL_LengthEncoding.suffix
    (PV_CBL_ShaBitLength.bitLength (UScalar.cast .Usize buffer.pos) core.block_len)).val

def retained (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6)) : List U8 :=
  PV_CBL_PaddingModel.first (flatten 6 buffer.buffer) buffer.pos.val (suffix core buffer)

theorem retained_length (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6))
    (h : buffer.pos.val<64) : (retained core buffer).length=64 := by
  apply PV_CBL_PaddingLength.first_length
  · exact PV_CBL_GenericArrayPower.length 6 buffer.buffer
  · exact h
  · exact PV_DL_LengthEncoding.suffix_length _

theorem buffer_restored (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6))
    (h : buffer.pos.val<64) :
    flatten 6 (PV_DL_StorageBuild.build 6 (fun i => (retained core buffer)[i]!))=
      retained core buffer :=
  PV_DL_StorageBuild.reconstruct 6 _ (retained_length core buffer h)

theorem output_restored (state : PV_DL_ShaFinal.State) :
    flatten 5 (PV_DL_StorageBuild.build 5 (fun i => (PV_DL_ShaSerialize.array state).val[i]!))=
      (PV_DL_ShaSerialize.array state).val :=
  PV_DL_StorageBuild.from32_value (PV_DL_ShaSerialize.array state)

/-- Same Eager private-state invariant as the shipped buffer; no additional
compression success, backend equality, or finalizer-source premise. -/
theorem selected_native (base : ExternalTypes)
    (ops : @ExternalFuns (PV_DL_ShaSelected.Types base))
    (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (core : PV_DL_ShaFinal.Core) (buffer : Buffer (Storage U8 6))
    (out : PV_DL_ShaSelected.Output32 base) (h : buffer.pos.val<64) :
    @ExternalFuns.op205 (PV_DL_ShaSelected.Types base)
      (PV_DL_ShaSelected.selected base ops compress) core buffer out=
      PV_DL_ShaSelected.value base compress core buffer :=
  PV_DL_ShaSelected.selected_native base ops compress core buffer out (by rw [position];exact h)

#print axioms position
#print axioms suffix
#print axioms retained
#print axioms retained_length
#print axioms buffer_restored
#print axioms output_restored
#print axioms selected_native
end R1Z.PV_DL_ShaRestoration
