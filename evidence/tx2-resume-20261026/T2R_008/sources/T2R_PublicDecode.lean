import T2R_Public
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_PublicDecode
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical

/-- Only the accepted decoder call already contained in the shared SourceCuts. -/
theorem facts (pub proof : Slice U8)
    (statement : AspisS6CurrentAdapterCarrier.PoolV1PairForestTerminalStatementV1)
    (decoded : AspisS6CurrentCodecInstallation.decode pub = ok (.Ok statement)) :
    T2R_Public.Facts pub proof := by
  obtain ⟨encoded,returned,contents⟩ := AspisS6CurrentCodecInstallation.accepted_inverse pub statement decoded
  have size : pub.val.length = 1880 := by rw [← contents]; exact encoded.property
  have length : (bytesOf pub.val).length = 1880 := by simpa only [bytesOf,List.length_map] using size
  have fit := DrvC_PublicCarrier.fits pub size
  refine ⟨Par_Public.input pub proof size,rfl,rfl,rfl,length,fit,?_⟩
  intro tr same
  rw [same]
  exact fit

#print axioms facts
end AspisR1.T2R_PublicDecode
end
