import NKO_C05Source
import NKE_GeometryCuts
set_option autoImplicit false
noncomputable section
namespace NKO_C05
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Actual C07 geometry domain, after the pending bind, from the SAME C05
source reply. No allocation-success or geometry endpoint premise at a root. -/
theorem at_query (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry native : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (reply : R (verifier.Accumulator × verifier.BatchedWeights))
 (entered : Event.query proof p a g geometry pending reply∈
  (run wr rr merkle finish d pub proof ck hash none).events)
 (cut : NKE_GeometryCuts.Cut geometry native) :
 native=geometry ∧ NJJ_Common.query proof p a g none native pending 22#usize=
  NJJ_Common.query proof p a g none geometry pending 22#usize := by
 obtain ⟨_,inverseSize,lineSize⟩ := source wr rr merkle finish d pub proof ck hash _ entered
 have same := NKE_GeometryCuts.same geometry native inverseSize lineSize cut
 exact ⟨same,by rw [same]⟩
#print axioms at_query
end NKO_C05
