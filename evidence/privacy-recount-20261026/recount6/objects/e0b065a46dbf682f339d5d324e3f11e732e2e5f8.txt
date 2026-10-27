import R1Z.PV_AL_TypenumValue
import R1Z.PV_CBL_GenericArrayPower
import R1Z.PV_CBL_ShaTypes
import R1Z.ProverRwFullFuns
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_AL_SplitNativeShape
open ProverRwFull PV_CBL_GenericArrayPower
set_option autoImplicit false

abbrev Types := PV_CBL_LibraryShapeTypes.selectedTypes

def Size (base : ExternalTypes) : Nat → Type
  | 0 => @typenum.uint.UInt (Types base) typenum.uint.UTerm typenum.bit.B1
  | k+1 => @typenum.uint.UInt (Types base) (Size base k) typenum.bit.B0

def nativeTrait (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    (k : Nat) → generic_array.ArrayLength (Size base k) U8 (Storage U8 k) := by
  letI : ExternalTypes := Types base
  letI : ExternalFuns := PV_AL_TypenumSize.selected base ops
  exact fun
  | 0 =>
    typenum.uint.UIntNB1.Insts.Generic_arrayArrayLengthTGenericArrayImplOdd
      (typenum.uint.UTerm.Insts.Generic_arrayArrayLengthTArrayT0 U8)
  | k+1 =>
    typenum.uint.UIntNB0.Insts.Generic_arrayArrayLengthTGenericArrayImplEven
      (nativeTrait base ops k)

theorem native_zero (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    (nativeTrait base ops 0).typenummarker_traitsUnsignedInst.USIZE=
      PV_AL_TypenumValue.value 0 := rfl

theorem native_step (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (k : Nat) :
    (nativeTrait base ops (k+1)).typenummarker_traitsUnsignedInst.USIZE=
      (do let n ← (nativeTrait base ops k).typenummarker_traitsUnsignedInst.USIZE
          ok ((UScalar.cast .Usize 0#u8) ||| Usize.wrapping_shl n 1#u32)) := rfl

theorem native_value (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (k : Nat) :
    (nativeTrait base ops k).typenummarker_traitsUnsignedInst.USIZE=
      PV_AL_TypenumValue.value k := by
  induction k with
  | zero => exact native_zero base ops
  | succ k ih => rw [native_step,ih]; rfl

theorem native_size (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    (nativeTrait base ops 6).typenummarker_traitsUnsignedInst.USIZE=ok 64#usize := by
  rw [native_value,PV_AL_TypenumValue.value64]

theorem consumed_storage (base : ExternalTypes) :
    PV_CBL_ShaTypes.Blocks (Types base)=
      Slice (PV_CBL_LibraryShapes.GenericArray U8 (Size base 6) (Storage U8 6)) := rfl

#print axioms Size
#print axioms nativeTrait
#print axioms native_zero
#print axioms native_step
#print axioms native_value
#print axioms native_size
#print axioms consumed_storage
end R1Z.PV_AL_SplitNativeShape
