import XRq_SamplerInterface
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
noncomputable section
namespace XRq_GammaDecode

theorem decode (digits : Array U32 8#usize) :
 mapR AspisR1ClaimPreparedBridge.gammaToPublic
  (AspisR1GammaCaller.DigitsModel.candidateGammaHelpers.decode digits) =
 XRn_Join_Release.sampler.decode8 digits := by
 change mapR AspisR1ClaimPreparedBridge.gammaToPublic
   (do let x ← AspisR1Post25Sampler.sampler.decode8 digits
       ok ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
         ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩) = _
 rw [←XRo_Join_OrdinaryDecode.decode]
 simp only [mapR_bind,map_ok]
 rfl
#print axioms decode
end XRq_GammaDecode
