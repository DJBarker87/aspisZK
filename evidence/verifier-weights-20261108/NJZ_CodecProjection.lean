import NJZ_Echeck
import NJC_EReaderResults
set_option autoImplicit false
noncomputable section
namespace NJZ_CodecProjection
open NFU_Retarget
open Aeneas Aeneas.Std Result AspisR1
open CheckpointBytes3EDecode CheckpointBytes3EShape CheckpointBytes3Word

/-- One arbitrary actual little-endian word, retaining every source byte. -/
theorem word (b : Array U8 32#usize) (i : Fin 8) :
 (word32 b.to_slice b.property i).val=NJZ_Echeck.words b.val i := by
 have lookup (j : Nat) (hj : j<b.val.length) :
   b.val[j]?.getD 0#u8=b.val[j]'hj := by
  rw [List.getElem?_eq_getElem hj]
  rfl
 rw [word32,CheckpointBytes3WordMath.pack_value]
 simp [NJZ_Echeck.words,LPl.Echeck.word,LPl.Echeck.byte,
  List.getElem?_drop,List.getElem?_take,List.getElem?_eq_getElem,
  show 4*i.val<b.val.length by rw [b.property];change _<32;omega,
  show 4*i.val+1<b.val.length by rw [b.property];change _<32;omega,
  show 4*i.val+2<b.val.length by rw [b.property];change _<32;omega,
  show 4*i.val+3<b.val.length by rw [b.property];change _<32;omega]
 <;> simp only [lookup (4*i.val) (by rw [b.property];change _<32;omega),
  lookup (4*i.val+1) (by rw [b.property];change _<32;omega),
  lookup (4*i.val+2) (by rw [b.property];change _<32;omega),
  lookup (4*i.val+3) (by rw [b.property];change _<32;omega)]
 <;> omega

#print axioms word
end NJZ_CodecProjection
