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

#print axioms pending
#print axioms flush
#print axioms query
end NKE_CommonClauses
