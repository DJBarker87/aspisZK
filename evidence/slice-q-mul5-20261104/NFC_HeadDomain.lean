import NFC_WideCanonical
import NFA_SuffixFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_HeadDomain
open Aeneas Aeneas.Std Result NEV_DotCarrier
/-- The head domain follows from the actual checked constructor, without a
separate assumed normalization result or a new arithmetic replay. -/
theorem canonical (limbs : Array U64 8#usize) (out : NE)
    (run : NFA_SuffixFactor.scalarFinish limbs=ok out) : canonE out := by
  unfold NFA_SuffixFactor.scalarFinish at run
  iterate 16 obtain ⟨x,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o,construct,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some v =>
    have same : v=out := Result.ok.inj run
    subst v
    exact NFC_WideCanonical.from_limbs _ out construct
#print axioms canonical
end AspisR1.NFC_HeadDomain
end
