import NJZ_Echeck
import NJC_EReaderResults
set_option autoImplicit false
noncomputable section
namespace NJZ_CodecProjection
open Aeneas Aeneas.Std Result AspisR1
open CheckpointBytes3EDecode CheckpointBytes3EShape CheckpointBytes3Word

/-- One arbitrary actual little-endian word, retaining every source byte. -/
theorem word (b : Array U8 32#usize) (i : Fin 8) :
 (word32 b.to_slice b.property i).val=NJZ_Echeck.words b.val i := by
 rw [word32,CheckpointBytes3WordMath.pack_value]
 simp [NJZ_Echeck.words,LPt_LPl.Echeck.word,LPt_LPl.Echeck.byte,
  List.getElem?_drop,List.getElem?_take,List.getElem?_eq_getElem,
  show 4*i.val<b.val.length by rw [b.property];change _<32;omega,
  show 4*i.val+1<b.val.length by rw [b.property];change _<32;omega,
  show 4*i.val+2<b.val.length by rw [b.property];change _<32;omega,
  show 4*i.val+3<b.val.length by rw [b.property];change _<32;omega]
 <;> omega

#print axioms word
end NJZ_CodecProjection
