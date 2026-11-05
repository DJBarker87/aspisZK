import NHM_DotPacket
import NHI_Scalar
set_option autoImplicit false
namespace NHM_DotFinishCanonical
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem words (a b c d e f g h : U64) :
 canonE (NEI_WideConstruction.value (NHE_DotFinish.word a) (NHE_DotFinish.word b)
  (NHE_DotFinish.word c) (NHE_DotFinish.word d) (NHE_DotFinish.word e)
  (NHE_DotFinish.word f) (NHE_DotFinish.word g) (NHE_DotFinish.word h)) := by
 simp only [canonE,canonQ,canonC,LPi_CMProduct.Canon,NEI_WideConstruction.value,
  NHE_DotFinish.word,AspisR1CanonicalDotFinish.Proof.canonicalWord_val]
 all_goals omega

theorem source (before : NHM_DotPacket.Dot) (out : NE)
 (run : FIo_Native.fast_pairing.EbyKDot.finish before=ok out) : canonE out := by
 rcases before with ⟨⟨left⟩,⟨right⟩,count⟩
 obtain ⟨a,b,c,d,hl⟩ := NGM_ArrayFour.shape left
 obtain ⟨e,f,g,h,hr⟩ := NGM_ArrayFour.shape right
 subst left
 subst right
 rw [NHE_DotFinish.native] at run
 cases Result.ok.inj run
 exact words a b c d e f g h

#print axioms words
#print axioms source
end NHM_DotFinishCanonical
