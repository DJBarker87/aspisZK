import XRo_Join_QmSampler
import XRo_Join_TranscriptBlock
import CurrentPreparedScratchModel
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport XRo_Join_ResultPair
set_option autoImplicit false
namespace XRo_Join_PreparedBoundaries

def query {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :=
 mapR (fun p => (inner id ce p.1,ct p.2)) (XRn_Join_Release.transcript.Transcript.queries (ed D) (et t) row payload)
def cachedClaim {H : Type} (D : C.D H) (sem : C.Sem H) (y1 : Slice U8)
 (inactive : C.E) (g : Array C.E 29#usize) (kappa : C.E) :=
 mapR (inner id ce) (verifier.prepared_claim (ed D) (es sem) y1 inactive g kappa)

def sampling : AspisR1PublicPreparation.PreparedModel.Boundaries where
 toBytes := aspis_core.field.wide_exact.WideExact.to_le_bytes
 fromQm := fun q=>aspis_core.field.wide_exact.WideExact.from_qm31 (eq q)
 ordinary := XRn_Join_Release.sampler.ordinary_sample
 gamma := XRn_Join_Release.sampler.gamma_sample
 queries := query
 claim := fun D sem y1 inactive gamma kappa => do
   let g ← XRn_Join_Release.weights.powers 29#usize gamma
   cachedClaim D sem y1 inactive g kappa

def boundaries : AspisR1PublicPreparation.PreparedScratchModel.Boundaries where
 sampling := sampling
 powers := XRn_Join_Release.weights.powers
 claim := cachedClaim

/-- This concrete dictionary is release-backed. Equality to the ADOPTED
installed dictionary is a separate obligation, not a hypothesis hidden here. -/
theorem legacy_claim_unused
 (legacy : {H : Type} → C.D H → C.Sem H → Slice U8 → C.E → C.E → C.E →
   Result (core.result.Result C.E C.Err))
 {H : Type} (D : C.D H) (sem : C.Sem H) (v : C.View) (hash : H)
 (g : Array C.E 29#usize) :
 AspisR1PublicPreparation.PreparedScratchModel.prepare
   {boundaries with sampling:={sampling with claim:=legacy}} D sem v hash g =
 AspisR1PublicPreparation.PreparedScratchModel.prepare boundaries D sem v hash g := rfl

#print axioms legacy_claim_unused
#print AspisR1PublicPreparation.PreparedScratchModel.prepare
end XRo_Join_PreparedBoundaries
