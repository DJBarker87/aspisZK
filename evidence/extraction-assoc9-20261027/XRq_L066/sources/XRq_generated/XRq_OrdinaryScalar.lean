import XRq_SamplerInterface
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
noncomputable section
namespace XRq_OrdinaryScalar
/-- The emitted scalar body with the excluded sampler interpreted explicitly. -/
def scalar {H : Type} (low : XRq_SamplerInterface.Low) (D : E.D H)
 (t : E.T H) (row : U8) (payload : Slice U8) (nonzero : Bool) : Result (C.E × E.T H) := do
 let (block,after) ← XRn_Join_Release.transcript.Transcript.block D t row payload
 let out ← if nonzero then XRq_SamplerInterface.gamma low block
   else XRq_SamplerInterface.ordinary low block
 let i ← lift (UScalar.cast .Usize row)
 XRn_Join_Release.trace.value 4#u16 i out
 ok (out,after)

theorem raw {H : Type} (D : E.D H) (t : E.T H)
 (row : U8) (payload : Slice U8) (nonzero : Bool) :
 scalar XRn_Join_Release.sampler.low_base_p_digits D t row payload nonzero =
 XRn_Join_Release.transcript.Transcript.scalar D t row payload nonzero := rfl

/-- Arbitrary transcript, payload and row; full fail/div and state preserved. -/
theorem ordinary {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (p.1,ct p.2))
  (scalar AspisR1Post25Sampler.sampler.low_base_p_digits (ed D) (et t) row payload false) =
 AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
  D t row payload false := by
 unfold scalar AspisR1PublicPreparation.PreparedModel.scalar
 rw [←XRo_Join_TranscriptBlock.block]
 simp only [mapR_bind,bind_map,ite_false]
 apply congrArg (fun k => XRn_Join_Release.transcript.Transcript.block (ed D) (et t) row payload >>= k)
 funext p
 rw [XRq_SamplerInterface.ordinary_cohort]
 simp only [mapR_bind,map_ok]
 rfl
#print axioms raw
#print axioms ordinary
end XRq_OrdinaryScalar
