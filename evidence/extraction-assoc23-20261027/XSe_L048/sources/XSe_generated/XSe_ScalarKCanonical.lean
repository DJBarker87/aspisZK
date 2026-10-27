import XSe_SamplerCanonical
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSe_ScalarKCanonical
/-- Canonicality at the actual scalar_k return; no successful sample premise. -/
theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
 (before after : transcript.Transcript H) (row : U8) (payload : Slice U8)
 (q : aspis_core.field.QM31)
 (run : transcript.Transcript.scalar_k D before row payload=ok (q,after)) :
 XRp_PowersQAdd.CanonicalQ q := by
 unfold transcript.Transcript.scalar_k at run
 obtain ⟨block,t,_,run⟩ := pair_bind_success _ _ _ run
 obtain ⟨sample,hsample,run⟩ := bind_success _ _ _ run
 obtain ⟨index,_,run⟩ := bind_success _ _ _ run
 obtain ⟨logged,_,run⟩ := bind_success _ _ _ run
 have same := congrArg Prod.fst (Result.ok.inj run)
 change sample=q at same
 rw [←same]
 exact XSe_SamplerCanonical.source block sample hsample
#print axioms source
end XSe_ScalarKCanonical
