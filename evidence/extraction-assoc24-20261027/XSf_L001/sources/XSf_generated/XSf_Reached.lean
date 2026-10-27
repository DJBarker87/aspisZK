import XSa_CachedClaim
import XRy_PreparePowers
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XSf_Reached

theorem kappa {H : Type} (D : C.D H) (before after : C.T H)
 (row : U8) (payload : Slice U8) (out : C.E)
 (h : AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
   D before row payload false=ok (out,after)) : XRy_WideMultiply.Canonical out := by
 exact AspisR1Post25SamplerOrdinaryCallbackV2.scalar_candidate_ordinary_canonical
   _ D before after row payload out h

theorem parsed (s : Slice U8) (out : C.E)
 (h : _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes s=ok (some out)) :
 XRy_WideMultiply.Canonical out := by
 rw [XSa_ParserTotal.bytes] at h
 cases hr : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes s with
 | fail e => simp only [hr,mapR] at h; cases h
 | div => simp only [hr,mapR] at h; cases h
 | ok opt =>
   cases opt with
   | none => simp only [hr,mapR,Option.map_none] at h; cases h
   | some w =>
     simp only [hr,mapR,Option.map_some,Result.ok.injEq,Option.some.injEq] at h
     subst out
     obtain ⟨_,arr,_,hc,he⟩ := AspisR1.ExtractedRecordByteCanonicality.slice_success s w hr
     rw [he]
     exact ⟨⟨⟨hc 0,hc 1⟩,⟨hc 2,hc 3⟩⟩,⟨⟨hc 4,hc 5⟩,⟨hc 6,hc 7⟩⟩⟩

#print axioms kappa
#print axioms parsed
end XSf_Reached
