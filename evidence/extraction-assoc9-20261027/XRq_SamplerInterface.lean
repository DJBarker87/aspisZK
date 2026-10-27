import XRo_Join_OrdinaryDecode
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
noncomputable section
namespace XRq_SamplerInterface
/-- The excluded native leaf has its original complete Result carrier. -/
abbrev Low := Array U8 32#usize → Result (Array U32 8#usize × U32)
/-- Exact emitted ordinary continuation, with only the excluded leaf abstracted. -/
def ordinary (low : Low) (block : Array U8 32#usize) : Result C.E := do
  let (digits,_) ← low block
  XRn_Join_Release.sampler.decode8 digits
/-- Exact emitted gamma continuation; add and decode are still emitted bodies. -/
def gamma (low : Low) (block : Array U8 32#usize) : Result C.E := do
  let (digits,quotient) ← low block
  let i ← quotient + 1#u32
  let (wrapped,digits1) ← XRn_Join_Release.sampler.add_small_base_p digits i
  let digits2 ← if wrapped then do
    let (_,digits3) ← XRn_Join_Release.sampler.add_small_base_p digits1 1#u32
    ok digits3
    else ok digits1
  XRn_Join_Release.sampler.decode8 digits2

theorem raw_ordinary (block : Array U8 32#usize) :
 ordinary XRn_Join_Release.sampler.low_base_p_digits block =
 XRn_Join_Release.sampler.ordinary_sample block := rfl

theorem raw_gamma (block : Array U8 32#usize) :
 gamma XRn_Join_Release.sampler.low_base_p_digits block =
 XRn_Join_Release.sampler.gamma_sample block := rfl

/-- Complete Result equality for every block; this uses the cohort leaf,
not the defective emitted low sampler. Native P6 remains LPk_'s obligation. -/
theorem ordinary_cohort (block : Array U8 32#usize) :
 ordinary AspisR1Post25Sampler.sampler.low_base_p_digits block =
 XRo_Join_Installed.actual.sampling.ordinary block := by
 rw [XRo_Join_OrdinaryDecode.ordinary_slot]
 unfold ordinary AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
   AspisR1Post25Sampler.sampler.ordinary_sample
 change _ = mapR AspisR1Post25SamplerPreparedCarrier.candidateToPE _
 simp only [mapR_bind]
 apply congrArg (fun k => AspisR1Post25Sampler.sampler.low_base_p_digits block >>= k)
 funext p
 exact (XRo_Join_OrdinaryDecode.decode p.1).symm

/-- Transport a proved native leaf equality; the premise is solely the leaf,
not the desired ordinary output. No native implementation is invented here. -/
theorem ordinary_native (native : Low)
 (leaf : ∀ block, native block = AspisR1Post25Sampler.sampler.low_base_p_digits block)
 (block : Array U8 32#usize) :
 ordinary native block = XRo_Join_Installed.actual.sampling.ordinary block := by
 unfold ordinary
 rw [leaf block]
 exact ordinary_cohort block

#print axioms raw_ordinary
#print axioms raw_gamma
#print axioms ordinary_cohort
#print axioms ordinary_native
end XRq_SamplerInterface
