import NKE_PendingAtSource
import NJR_ReservationSites
set_option autoImplicit false
noncomputable section
namespace NKO_C06
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- The actual allocation reply can enter C07 only with the pending value
constructed from THAT accumulator. Both reserve outcomes remain universal. -/
theorem pending_eq (rr : NP6_StdModel.Reservation) (a : verifier.Accumulator)
 (width : a.weights.val.length=64) (pending : verifier.BatchedWeights)
 (call : NJJ_Common.pending rr a.weights.deref=ok (.Ok pending)) :
 pending=NFW_QueryResume.pending a := by
 rw [NJR_ReservationSites.pending rr a width] at call
 cases rr with
 | Err error => cases call
 | Ok unit =>
  cases unit
  exact (core.result.Result.Ok.inj (Result.ok.inj call)).symm

/-- Actual C06 return widths and terms, including allocation-failure exclusion
by the internal branch equation. No allocation success premise at a root. -/
theorem returned (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (weights : Slice aspis_core.field.QM31) (pending : verifier.BatchedWeights)
 (entered : Event.pending weights (ok (.Ok pending))∈
  (run wr rr merkle finish d pub proof ck hash none).events) :
 pending.raw.val.length=64 ∧ pending.terms=0#usize := by
 obtain ⟨width,_⟩ := NKE_CommonDomain.source wr rr merkle finish d pub proof ck hash _ entered
 have source := NKE_PendingAtSource.source wr rr merkle finish d pub proof ck hash weights _ entered
 cases rr with
 | Err error => cases source
 | Ok unit =>
  cases unit
  change (ok (.Ok pending) : R verifier.BatchedWeights)=ok (.Ok
   (⟨NKE_PendingNative.states weights (NKE_CommonNative.zeros weights) 64,0#usize⟩ : verifier.BatchedWeights)) at source
  have same := core.result.Result.Ok.inj (Result.ok.inj source)
  rw [same]
  refine ⟨?_,rfl⟩
  change (NKE_Stores.G _ _ _).length=64
  rw [NKE_Stores.length]
  simpa only [NKE_CommonNative.zeros,List.length_replicate] using width
#print axioms pending_eq
#print axioms returned
end NKO_C06
