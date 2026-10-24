import Port1_Driver

/-! The source lift consumes physical bytes, whereas the headline join ranges
over an independent logical proof. Nontrivial source acceptance cannot refine
that all-input model without a carrier construction/transport argument. This
is a statement about the quantified interface, not a shipped-code attack. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_CarrierObstruction
open Aeneas Aeneas.Std Result VTop_Stages VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortFrozen2Join

/-- A constant erased constructor cannot occupy both the initial and later
rows. No oracle, field arithmetic, valid fixture or large reduction is used. -/
theorem constant_rejected (D : LiteralByteProtocol.Decoder)
    (pub : RawCutProverCompiler.Public) (stored : Bytes)
    (message : LiteralTranscript.Message) (H : Bytes → State) :
    (eval H (verifier D OraclePortFrozen2.dV_frozen2
      ⟨pub, (fun _ => message), stored⟩)).2 = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  change (eval H (OracleDecisionFeasibilityCore.verifier D
    (OraclePortFrozen2.dV_frozen2 stored) pub (fun _ => message))).2 = true at accepted
  rw [OracleDecisionFeasibilityBudget.verifier_eval] at accepted
  have terminal : (eval H (OraclePortFrozen2.dV_frozen2 stored
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub (fun _ => message) 33))
      (LiteralTranscript.erase message))).2 = true := accepted
  have guard := (OraclePortFrozen2.accepted_details stored _ _ H terminal).1
  have shape := D0ScheduleAdmission.shape_of_schedule D H pub (fun _ => message) guard.2.1
  cases message with
  | initial root word => exact shape 31 (by decide)
  | payload bytes => exact shape 0 (by decide)
  | c2 bytes word => exact shape 0 (by decide)
  | second bytes word => exact shape 0 (by decide)

/-- The actual source arguments contain no separate logical proof function. -/
theorem proof_irrelevant (adapter : AdapterRw.Ops) (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (i : Input)
    (pf : RawCutProverCompiler.Proof) :
    Port1_Driver.rust adapter impl D hash {i with proof := pf} =
      Port1_Driver.rust adapter impl D hash i := rfl

/-- Consequently the requested unrestricted raw join would force this natural
source lift to reject every input. Per-body equalities cannot repair the
independent logical proof carrier. No source acceptance witness is assumed
silently or claimed proved here. -/
theorem raw_join_forces_rejection (adapter : AdapterRw.Ops) (impl : Implementation)
    {Hash : Type} (digest : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (decoder : LiteralByteProtocol.Decoder)
    (join : AcceptedVerifierJoin (Port1_Driver.rust adapter impl digest hash)
      (verifier decoder OraclePortFrozen2.dV_frozen2)) (H : Bytes → State) (i : Input) :
    (eval H (Port1_Driver.rust adapter impl digest hash i)).2 ≠ true := by
  intro accepted
  let bad : Input := {i with proof := fun _ => i.proof 0}
  have before : (eval H (Port1_Driver.rust adapter impl digest hash bad)).2 = true := accepted
  have same := congrArg Prod.snd (join H bad before)
  have reject := constant_rejected decoder i.statement i.stored (i.proof 0) H
  change (eval H (Port1_Driver.rust adapter impl digest hash bad)).2 =
    (eval H (verifier decoder OraclePortFrozen2.dV_frozen2
      ⟨i.statement,(fun _ => i.proof 0),i.stored⟩)).2 at same
  rw [before, reject] at same
  cases same

#print axioms constant_rejected
#print axioms proof_irrelevant
#print axioms raw_join_forces_rejection
end AspisR1.Port1_CarrierObstruction
end
