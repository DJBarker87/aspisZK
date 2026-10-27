import XSf_Reached
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRn_Join_Release
set_option autoImplicit false
namespace XSf_View

theorem inactive (proof semantic y1 : Slice U8) (v : verifier.View)
 (run : verifier.candidate.wide_view proof semantic y1=ok (.Ok v)) :
 XRy_WideMultiply.Canonical (cview v).inactive := by
 unfold verifier.candidate.wide_view at run
 obtain ⟨bytes,_,run⟩ := bind_success _ _ _ run
 obtain ⟨opt,hparse,run⟩ := bind_success _ _ _ run
 cases opt with
 | none => cases run
 | some x =>
   have hx := XSf_Reached.parsed bytes x hparse
   obtain ⟨round0,_,run⟩ := bind_success _ _ _ run
   obtain ⟨root,_,run⟩ := bind_success _ _ _ run
   obtain ⟨root32,_,run⟩ := bind_success _ _ _ run
   obtain ⟨round1,_,run⟩ := bind_success _ _ _ run
   obtain ⟨final,_,run⟩ := bind_success _ _ _ run
   cases run
   exact hx

#print axioms inactive
end XSf_View
