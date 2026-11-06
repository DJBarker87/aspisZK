import NKE_EventAll
import NKE_QueryReturn
set_option autoImplicit false
noncomputable section
namespace NKE_CommonClauses
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
open NJU_CommonObserved
/-- Selected source clauses, for attaching native pending/flush/query windows.
Other events remain explicitly outside this partial association. -/
def Clause (reservation : NP6_StdModel.Reservation) : Event → Prop
 | .pending weights reply => reply=NJJ_Common.pending reservation weights
 | .flush pending weights reply => reply=Port3_FlushInstall.flush pending weights
 | .query _ _ _ _ _ _ reply => NKE_QueryReturn.observed reply=reply
 | _ => True

theorem pending (r : NP6_StdModel.Reservation) (weights : Slice aspis_core.field.QM31) :
 Clause r (.pending weights (NJJ_Common.pending r weights)) := rfl

theorem flush (r : NP6_StdModel.Reservation) (pending : verifier.BatchedWeights)
 (weights : Slice aspis_core.field.QM31) :
 Clause r (.flush pending weights (Port3_FlushInstall.flush pending weights)) := rfl

theorem query (r : NP6_StdModel.Reservation) (proof : Slice U8)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (reply : Result NKE_QueryReturn.Reply) :
 Clause r (.query proof p a g geometry pending reply) := NKE_QueryReturn.observed_exact reply

/-- One actual common log, without a free endpoint or a second invocation. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_EventAll.Holds (Clause rr) (run wr rr merkle finish d pub proof ck hash none) := by
 unfold run
 repeat' first
 | apply NKE_EventAll.bind_all
 | intro value
 | exact NKE_EventAll.lift_all _ _
 | exact NKE_EventAll.pure_all _ _
 | (apply NKE_EventAll.record_all; first | rfl | exact True.intro | exact NKE_QueryReturn.observed_exact _)
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
#print axioms pending
#print axioms flush
#print axioms query
#print axioms source
end NKE_CommonClauses
