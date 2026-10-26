import F3T_CanonicalJoin
import F3T_Decision
import Port1_CarrierObstruction
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Unrestricted
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass F3T_CanonicalJoin

theorem constant_rejected (D : LiteralByteProtocol.Decoder) (i : F3_Model.Input)
    (message : LiteralTranscript.Message) (H : Bytes → State) :
    (eval H (F3_Model.verifier D {i with proof:=fun _=>message})).2=false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  change (eval H (OracleDecisionFeasibilityCore.verifier D
    (F3_Model.decision i.physical i.stored) i.semantic.value (fun _=>message))).2=true at accepted
  rw [OracleDecisionFeasibilityBudget.verifier_eval] at accepted
  have terminal : (eval H (F3_Model.decision i.physical i.stored
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H i.semantic.value (fun _=>message) 33))
      (LiteralTranscript.erase message))).2=true := accepted
  have guard := (F3T_Decision.accepted_details i.physical i.stored _ _ H terminal).1
  have shape := D0ScheduleAdmission.shape_of_schedule D H i.semantic.value (fun _=>message) guard.2.1
  cases message with
  | initial root word=>exact shape 31 (by decide)
  | payload bytes=>exact shape 0 (by decide)
  | c2 bytes word=>exact shape 0 (by decide)
  | second bytes word=>exact shape 0 (by decide)

theorem no_global_join (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (physical : Physical rust) (H : Bytes → State) (i : F3_Model.Input)
    (accepted : (eval H (rust i)).2=true) : ¬ RawJoin D rust := by
  intro join
  let bad : F3_Model.Input := {i with proof:=fun _=>i.proof 0}
  have source : rust bad=rust i := physical _ _ rfl rfl
  have before : (eval H (rust bad)).2=true := by rw [source];exact accepted
  have same := congrArg Prod.snd (join H bad before)
  rw [before,constant_rejected D i (i.proof 0) H] at same
  cases same

#print axioms constant_rejected
#print axioms no_global_join
end AspisR1.F3T_Unrestricted
end
