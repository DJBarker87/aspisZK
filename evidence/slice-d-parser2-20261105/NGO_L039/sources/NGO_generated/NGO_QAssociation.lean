import NGO_WordLaw
import NGD_QDecodeLaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_QAssociation
abbrev ActualQ := AspisR1DecodeKFullV10.aspis_core.field.QM31
/-- Complete original four-word tower, with no coordinate permutation. -/
def toActual (q : NGO_QRef.QM31) : ActualQ :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromActual (q : ActualQ) : NGO_QRef.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
theorem roundtrip (q : ActualQ) : toActual (fromActual q)=q := by cases q; rfl
theorem reverse (q : NGO_QRef.QM31) : fromActual (toActual q)=q := by cases q; rfl
-- Word values are the retained codec's four exact limb windows.
def word (arr : Array U8 16#usize) (limb : Fin 4) : U32 :=
  AspisR1.AeneasWordCodec.aeneasWord
    (AspisR1.RetainedFieldByteCodec.qm31LimbBytes
      (AspisR1.CandidateParserByteOrder.arrayBytes16 arr) limb)
theorem word_value (arr : Array U8 16#usize) (limb : Fin 4) :
    (word arr limb).val =
      (AspisR1.RetainedFieldByteCodec.decodeWordLE
        (AspisR1.RetainedFieldByteCodec.qm31LimbBytes
          (AspisR1.CandidateParserByteOrder.arrayBytes16 arr) limb)).val :=
  AspisR1.AeneasWordCodec.aeneasWord_val_eq _
theorem segment_word (arr : Array U8 16#usize) (i : Usize) (limb : Fin 4)
    (position : i.val=4*limb.val) (bound : i.val≤12) :
    core.num.U32.from_le_bytes (NGO_WordLaw.segment arr i bound)=word arr limb := by
  unfold word AspisR1.AeneasWordCodec.aeneasWord
  congr 1
  apply Subtype.ext
  simp only [NGO_WordLaw.segment,Array.make]
  simp [AspisR1.RetainedFieldByteCodec.qm31LimbBytes,
    AspisR1.RetainedFieldByteCodec.limbByteIndex_val,
    AspisR1.CandidateParserByteOrder.arrayBytes16,
    AspisV8R19.SqueezeOracleBridge.word_roundtrip,position,Nat.add_comm]
#print axioms roundtrip
#print axioms reverse
#print axioms word_value
#print axioms segment_word
end NGO_QAssociation
