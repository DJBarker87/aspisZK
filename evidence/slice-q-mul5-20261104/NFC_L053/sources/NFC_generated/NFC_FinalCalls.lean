import NFC_ChainAssociation
import NFC_AddDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_FinalCalls
open Aeneas Aeneas.Std Result NEV_DotCarrier NFC_TailTrace
/-- Unrestricted actual finish totality: the opaque native reply covers every
actual receiver, not just an assumed successful finish observation. -/
theorem finish (state : Acc) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish state=ok out ∧ canonE out := by
  rcases state with ⟨⟨left⟩,⟨right⟩,count⟩
  obtain ⟨a,b,c,d,hl⟩:=NFC_ArrayFour.shape left
  obtain ⟨e,f,g,h,hr⟩:=NFC_ArrayFour.shape right
  subst left
  subst right
  obtain ⟨out,call,_⟩:=NEI_PublicDotFinishValues.source a b c d e f g h count
  exact ⟨out,call,NFC_TailState.finish_canonical _ out call⟩

/-- Final-add domain is established by head/tail construction upstream. -/
theorem add (left right : NE) (hl : canonE left) (hr : canonE right) :
    ∃ out,FIo_Native.aspis_core.field.wide_exact.WideExact.add left right=ok out ∧ canonE out :=
  NFC_AddDomain.total left right hl hr
#print axioms finish
#print axioms add
end AspisR1.NFC_FinalCalls
end
