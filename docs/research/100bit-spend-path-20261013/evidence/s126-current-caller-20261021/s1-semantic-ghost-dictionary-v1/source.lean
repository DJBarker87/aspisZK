import S1SemanticFinishModelV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticGhost
open Aeneas Aeneas.Std Result

theorem new_error {H : Type} (first second : aspis_core.Digest32 H) :
    r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError first=
      r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError second := by
  unfold r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError
    r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once
  rfl

theorem public_error {H : Type} (first second : aspis_core.Digest32 H) :
    r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError first=
      r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError second := by
  unfold r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
    r1_semantic.public_transcript.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  rfl

theorem finish_error {H : Type} (first second : aspis_core.Digest32 H) :
    FinishModel.closureFn11 first=FinishModel.closureFn11 second := by
  unfold FinishModel.closureFn11 FinishModel.closureFn10
  rfl

theorem finish5 {H : Type} (first second : aspis_core.Digest32 H) :
    FinishModel.closureFn5 first=FinishModel.closureFn5 second := by
  unfold FinishModel.closureFn5 FinishModel.closureFn4 FinishModel.closureFn3 FinishModel.closureFn2
  rfl

theorem finish9 {H : Type} (first second : aspis_core.Digest32 H) :
    FinishModel.closureFn9 first=FinishModel.closureFn9 second := by
  unfold FinishModel.closureFn9 FinishModel.closureFn8 FinishModel.closureFn7 FinishModel.closureFn6
  rfl

theorem state {H : Type} (first second : aspis_core.Digest32 H) (t : r1_wire.SemanticTranscript H) :
    r1_wire.SemanticTranscript.impl.state first t=r1_wire.SemanticTranscript.impl.state second t := by
  unfold r1_wire.SemanticTranscript.impl.state
  rfl

#print axioms new_error
#print axioms public_error
#print axioms finish_error
#print axioms finish5
#print axioms finish9
#print axioms state
end AspisR1PublicPreparation.S1SemanticGhost
