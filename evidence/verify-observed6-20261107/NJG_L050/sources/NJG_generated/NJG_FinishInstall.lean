import NJG_FinishClosures
set_option autoImplicit false
namespace AspisR1.NJG_FinishInstall
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Fix the two std boundary implementations to their actual source forms;
all protocol children remain the caller's dictionary, without success laws. -/
def model (F : FinishModel.Boundaries) : FinishModel.Boundaries :=
 {F with
  fromFn:=OraclePortStdBuilder.fromFn
  unwrapRoot:=core.result.Result.unwrap core.fmt.DebugTryFromSliceError}

def install {H : Type} (R : RoundModel.Boundaries) (F : FinishModel.Boundaries) :
 NJG_FinishBody.Boundaries H where
 fromFn:=OraclePortStdBuilder.fromFn
 mapError:=core.result.Result.map_err
 qEq:=aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq
 pointEq:=FinishModel.pointEq
 add:=F.add
 mul:=F.mul
 mask:=F.mask
 terminal:=F.terminal
 claims:=F.claims
 rounds:=RoundModel.rounds R
 record:=r1_wire.Prefix.validated_record
 payload:=FinishModel.payload
 circle:=FinishModel.circle_validated (model F)
 state:=r1_wire.SemanticTranscript.impl.state
 decode:=R.decode

theorem first_callback {H : Type} (D : aspis_core.Digest32 H) :
 NJG_FinishBody.r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 D=
 FinishModel.closureFn9 D := rfl

theorem error_callback {H : Type} (D : aspis_core.Digest32 H) :
 NJG_FinishBody.r1_semantic.verify_finish.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError D=
 FinishModel.closureFn11 D := rfl

/-- Frozen emitted finish body to adopted complete Result, with protocol child
functions substituted at the SAME call arguments. No output-success or child
endpoint clause is a hypothesis. This is body/model support; native stage cuts,
child domains/packets and std interpretation are still required for row136. -/
theorem source {H : Type} (R : RoundModel.Boundaries) (F : FinishModel.Boundaries)
 (D : aspis_core.Digest32 H) (pubdata : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges) :
 NJG_FinishBody.r1_semantic.verify_finish (install R F) D pubdata pre t challenges none=
 FinishModel.finish R (model F) D pubdata pre t challenges none := by
 unfold NJG_FinishBody.r1_semantic.verify_finish FinishModel.finish
 simp only [install,model,NJG_FinishBody.r1_semantic.mark,bind_tc_ok,
  first_callback,error_callback,NJG_FinishClosures.second_array,
  NJG_FinishBody.qCmp,VerifyPrefix.mark]

#print axioms first_callback
#print axioms error_callback
#print axioms source
end AspisR1.NJG_FinishInstall
