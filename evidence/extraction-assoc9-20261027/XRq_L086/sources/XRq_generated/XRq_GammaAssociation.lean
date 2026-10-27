import XRq_GammaDecode
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
noncomputable section
namespace XRq_GammaAssociation
/-- This precise adapter equality remains OPEN, not native trust or a fixture. -/
def AddAssociation : Prop := ∀ (digits : Array U32 8#usize) (n : U32),
 XRn_Join_Release.sampler.add_small_base_p digits n =
 AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits n

theorem gamma (add : AddAssociation) (block : Array U8 32#usize) :
 XRq_SamplerInterface.gamma AspisR1Post25Sampler.sampler.low_base_p_digits block =
 XRo_Join_Installed.actual.sampling.gamma block := by
 change _ = AspisR1ClaimPreparedBridge.candidateGammaPublic block
 unfold XRq_SamplerInterface.gamma AspisR1ClaimPreparedBridge.candidateGammaPublic
   AspisR1GammaCaller.sampler.gamma_sample
 change _ = mapR AspisR1ClaimPreparedBridge.gammaToPublic _
 simp only [mapR_bind]
 apply congrArg (fun k => AspisR1Post25Sampler.sampler.low_base_p_digits block >>= k)
 funext p
 change _ = mapR AspisR1ClaimPreparedBridge.gammaToPublic
   (do let i ← p.2+1#u32
       let (wrapped,digits1) ← AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p p.1 i
       let digits2 ← if wrapped then do
         let (_,digits3) ← AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits1 1#u32
         ok digits3 else ok digits1
       AspisR1GammaCaller.DigitsModel.candidateGammaHelpers.decode digits2)
 simp only [mapR_bind]
 apply congrArg (fun k => (p.2+1#u32) >>= k)
 funext i
 rw [add p.1 i]
 apply congrArg (fun k => AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p p.1 i >>= k)
 funext q
 rcases q with ⟨wrapped,digits1⟩
 change (do
   let digits2 ← if wrapped then do
     let (_,digits3) ← XRn_Join_Release.sampler.add_small_base_p digits1 1#u32
     ok digits3 else ok digits1
   XRn_Join_Release.sampler.decode8 digits2) =
   (do
     let digits2 ← if wrapped then do
       let (_,digits3) ← AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits1 1#u32
       ok digits3 else ok digits1
     mapR AspisR1ClaimPreparedBridge.gammaToPublic
       (AspisR1GammaCaller.DigitsModel.candidateGammaHelpers.decode digits2))
 rw [add digits1 1#u32]
 apply congrArg (fun k =>
   (if wrapped then do
     let (_,digits3) ← AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits1 1#u32
     ok digits3 else ok digits1) >>= k)
 funext digits2
 exact (XRq_GammaDecode.decode digits2).symm
#print axioms gamma
end XRq_GammaAssociation
