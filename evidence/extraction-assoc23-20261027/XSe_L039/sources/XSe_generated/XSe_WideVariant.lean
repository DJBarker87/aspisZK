import XSe_PreparedVariant
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSe_WideVariant
/-- Actual compact-view call sites always construct the S2 variant. -/
theorem source (proof semantic y1 : Slice U8) (v : verifier.View)
 (run : verifier.candidate.wide_view proof semantic y1=ok (.Ok v)) : v.variant=.S2 := by
 unfold verifier.candidate.wide_view at run
 obtain ⟨bytes,_,run⟩ := bind_success _ _ _ run
 obtain ⟨inactive,_,run⟩ := bind_success _ _ _ run
 cases inactive with
 | none => cases run
 | some inactive =>
  obtain ⟨round0,_,run⟩ := bind_success _ _ _ run
  obtain ⟨root0,_,run⟩ := bind_success _ _ _ run
  obtain ⟨root,_,run⟩ := bind_success _ _ _ run
  obtain ⟨round1,_,run⟩ := bind_success _ _ _ run
  obtain ⟨finalMessage,_,run⟩ := bind_success _ _ _ run
  cases core.result.Result.Ok.inj (Result.ok.inj run)
  rfl
#print axioms source
end XSe_WideVariant
