import NFA_ArrayShape
import NEI_WideCtorLaw
import NEV_DotCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_WideCanonical
open Aeneas Aeneas.Std Result NEV_DotCarrier
/-- Success of the actual checked constructor establishes every coordinate. -/
theorem from_limbs (words : Array U32 8#usize) (out : NE)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs words=ok (some out)) :
    canonE out := by
  obtain ⟨a,b,c,d,e,f,g,h,shape⟩:=NFA_ArrayShape.shape words
  unfold NFA_ArrayShape.pack at shape
  rw [shape,NEI_WideCtorLaw.limbs_result] at run
  split at run
  · rename_i valid
    have same := Option.some.inj (Result.ok.inj run)
    subst out
    rcases valid with ⟨ha,hb,hc,hd,he,hf,hg,hh⟩
    dsimp only [canonE,canonQ,canonC,NEI_WideCtorLaw.value]
    exact ⟨⟨⟨by scalar_tac,by scalar_tac⟩,⟨by scalar_tac,by scalar_tac⟩⟩,
      ⟨⟨by scalar_tac,by scalar_tac⟩,⟨by scalar_tac,by scalar_tac⟩⟩⟩
  · cases run
#print axioms from_limbs
end AspisR1.NFC_WideCanonical
end
