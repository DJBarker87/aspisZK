import NDF_ParserWord
set_option autoImplicit false
namespace NDI_HeaderShifts
open Aeneas Aeneas.Std Result

theorem byte8 (x : U8) : (UScalar.cast .Usize x) <<< 8#i32 =
    ok (⟨(BitVec.zeroExtend UScalarTy.Usize.numBits x.bv) <<< 8⟩ : Usize) := by
  have fit : 8<System.Platform.numBits := by have := System.Platform.le_numBits;omega
  change UScalar.shiftLeft_IScalar (UScalar.cast .Usize x) 8#i32 = _
  simp [UScalar.shiftLeft_IScalar,UScalar.shiftLeft,fit]
  rfl

theorem byte16 (x : U8) : (UScalar.cast .Usize x) <<< 16#i32 =
    ok (⟨(BitVec.zeroExtend UScalarTy.Usize.numBits x.bv) <<< 16⟩ : Usize) := by
  have fit : 16<System.Platform.numBits := by have := System.Platform.le_numBits;omega
  change UScalar.shiftLeft_IScalar (UScalar.cast .Usize x) 16#i32 = _
  simp [UScalar.shiftLeft_IScalar,UScalar.shiftLeft,fit]
  rfl

theorem byte24 (x : U8) : (UScalar.cast .Usize x) <<< 24#i32 =
    ok (⟨(BitVec.zeroExtend UScalarTy.Usize.numBits x.bv) <<< 24⟩ : Usize) := by
  have fit : 24<System.Platform.numBits := by have := System.Platform.le_numBits;omega
  change UScalar.shiftLeft_IScalar (UScalar.cast .Usize x) 24#i32 = _
  simp [UScalar.shiftLeft_IScalar,UScalar.shiftLeft,fit]
  rfl

#print axioms byte8
#print axioms byte16
#print axioms byte24
end NDI_HeaderShifts
