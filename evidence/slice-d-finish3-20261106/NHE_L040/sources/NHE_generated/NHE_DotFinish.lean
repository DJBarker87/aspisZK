import NHE_DotState
import NHE_RoundRef
import NFE_NEI_PublicDotFinishValues
set_option autoImplicit false
namespace NHE_DotFinish
open Aeneas Aeneas.Std Result AspisR1
abbrev word := AspisR1EbyKFinish.Proof.word

theorem word_eq (x : U32) (a : U64) (h : x.val=a.val%2147483647) : x=word a := by
 apply UScalar.eq_of_val_eq
 rw [AspisR1CanonicalDotFinish.Proof.canonicalWord_val]
 exact h

theorem native (a b c d e f g h : U64) (count : Usize) :
 FIo_Native.fast_pairing.EbyKDot.finish
  ⟨⟨Array.make 4#usize [a,b,c,d]⟩,⟨Array.make 4#usize [e,f,g,h]⟩,count⟩=
 ok (NEI_WideConstruction.value (word a) (word b) (word c) (word d) (word e) (word f) (word g) (word h)) := by
 obtain ⟨out,run,v0,v1,v2,v3,v4,v5,v6,v7⟩ := NFE_NEI_PublicDotFinishValues.source a b c d e f g h count
 have shape : out=NEI_WideConstruction.value (word a) (word b) (word c) (word d) (word e) (word f) (word g) (word h) := by
  apply NHE_RoundRef.words_injective
  simp only [NGM_RawWords.nativeWords,NEI_WideConstruction.value,word_eq _ _ v0,word_eq _ _ v1,word_eq _ _ v2,word_eq _ _ v3,word_eq _ _ v4,word_eq _ _ v5,word_eq _ _ v6,word_eq _ _ v7]
 rw [run,shape]

theorem cohort (d : NHE_DotState.Dot) :
 FIo_FieldBridge.map FIo_Install.fromE (FIo_Native.fast_pairing.EbyKDot.finish d)=
 (do let out ← AspisR1FinishDotSourceABI.finishFromPush (NHE_DotState.toPush d)
     ok (SAG_DotAdapter.toStageE out)) := by
 rcases d with ⟨⟨left⟩,⟨right⟩,count⟩
 obtain ⟨a,b,c,d,hl⟩ := NGM_ArrayFour.shape left
 obtain ⟨e,f,g,h,hr⟩ := NGM_ArrayFour.shape right
 subst left
 subst right
 rw [native]
 simp only [AspisR1FinishDotSourceABI.finishFromPush,AspisR1FinishDotSourceABI.toFinishState,NHE_DotState.toPush,AspisR1EbyKFinish.Proof.finish_eight,bind_tc_ok]
 rfl

#print axioms word_eq
#print axioms native
#print axioms cohort
end NHE_DotFinish
