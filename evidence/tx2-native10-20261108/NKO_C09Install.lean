import NKO_C09Source
import NKE_FinishSupplement
set_option autoImplicit false
noncomputable section
namespace NKO_C09
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- The actual finish event must follow all three checked current-proof slices.
A short proof never supplies a finish event, regardless of earlier error exits. -/
theorem bounds_at_actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) (reply : R Unit)
 (entered : Event.finish v p a reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 10055≤proof.val.length := by
 have facts := source wr rr merkle finish d pub proof ck hash _ entered
 have length := congrArg List.length facts.final
 rw [facts.final_size,List.length_take,List.length_drop] at length
 omega

/-- Apply the retained generalized (aw) child at the SAME actual View/p/a.
The domain is discharged internally; no history, raw canonicality, NoBad,
current-proof persistence or successful-finish premise is introduced. -/
theorem child_at_actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) (reply : R Unit)
 (entered : Event.finish v p a reply∈(run wr rr merkle finish d pub proof ck hash none).events)
 (r : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations) :
 let execution:=NJF_FinishObserved.G r loc v p a
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=execution.1 ∧
 NIW_AlignFinishComposedLog.forget execution=NIW_AlignFinishExecution.run r v p a ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 :=
 NKE_FinishSupplement.finish r loc proof v p a (source wr rr merkle finish d pub proof ck hash _ entered)
#print child_at_actual
#print axioms bounds_at_actual
#print axioms child_at_actual
end NKO_C09
