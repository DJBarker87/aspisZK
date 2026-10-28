import R1Z.PV_RunJoin_LedgerWorldFields
import R1Z.PV_RunJoin_BodyFootprint
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerWorldInvariant
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_LedgerWorld PV_RunJoin_ResultPost
variable [ExternalTypes]

def Invariant (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (initial : ProverCommitLedger36.State) (s : World) : Prop :=
  match s.entered with
  | none => s.model = initial
  | some path => s.model = (ProverCommitLedger36.reserve schedule unix path initial).2

def clear (s : World) : World := {s with entered := none}

theorem initial (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (s : World) :
    Invariant schedule unix s.model (clear s) := rfl

theorem callback (ops : ExternalFuns) (schedule : ProverCommitLedger36.Schedule)
    (unix : Bool) (address : Address) (s after : World)
    (statement nonce : Array U8 32#usize) (accepted : Bool)
    (run : reserve ops schedule unix address (clear s) statement nonce = .ok (accepted,after)) :
    Invariant schedule unix s.model after := by
  have written := PV_RunJoin_LedgerWorldFields.writeback ops schedule unix address
    (clear s) after statement nonce accepted run
  unfold Invariant
  rw [written.2]
  exact written.1

theorem caller (ops : ExternalFuns) (schedule : ProverCommitLedger36.Schedule)
    (unix : Bool) (address : Address) (s : World)
    (pub : Pub) (compiled : Compiled) (variant : transport.Variant) (hash : Hash) (secret : Secret) :
    letI : ExternalFuns := ops
    Post (fun out => Invariant schedule unix s.model out.2)
      (PV_RunJoin_GenericSourceCaller.caller (dictionary ops schedule unix address)
        pub compiled variant hash secret (clear s)) := by
  letI : ExternalFuns := ops
  apply PV_RunJoin_BodyFootprint.caller _ _ pub compiled variant hash secret (clear s)
  · exact initial schedule unix s
  · intro statement nonce accepted after run
    exact callback ops schedule unix address s after statement nonce accepted run

#print axioms initial
#print axioms callback
#print axioms caller
end R1Z.PV_RunJoin_LedgerWorldInvariant
