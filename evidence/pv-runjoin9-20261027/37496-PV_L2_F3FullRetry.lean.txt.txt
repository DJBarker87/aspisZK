import R1Z.PV_L2_F3FullSource
import R1Z.SideChannelL1AttemptRecord

/-! Ordered retry carrier with the full L1 record and owned-source read
prefixes. No callback or native event producer is postulated by this file.
Erasure is exact on retries and stops, not only published proofs. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F3FullRetry
open R1Z.SideChannelL1AttemptRecord
open R1Z.ProverCommitRetry34

structure Attempt (Proof : Type) where
  l1 : SideChannelL1AttemptRecord.Attempt Proof
  maskReads : List PV_L2_F3Recorded.Read
  entropyReads : List PV_L2_F3Recorded.Read
  /-- Actual ordered request/answer history must be supplied by the caller;
  the finite blockHash backend is not identified with an adaptive ROM. -/
  rom : List (List UInt8 × R0Z.FsStatement.OracleAnswer)

structure Run (Proof : Type) where
  attempts : List (Attempt Proof)
  result : Step (Published Proof)

def erase {Proof : Type} (r : Run Proof) : SideChannelL1AttemptRecord.Run Proof :=
  ⟨r.attempts.map Attempt.l1,r.result⟩

abbrev Owner (State Proof : Type) := Nat → State → Attempt Proof × State

def ownerL1 {State Proof : Type} (owner : Owner State Proof) :
    SideChannelL1AttemptRecord.Owner State Proof := fun index state =>
  let (record,after) := owner index state
  (record.l1,after)

def run {State Proof : Type} (owner : Owner State Proof) :
    Nat → Nat → State → Run Proof × State
  | 0,_,state => (⟨[],.stop .AttemptsExhausted⟩,state)
  | fuel+1,index,state =>
    let (record,after) := owner index state
    match record.l1.result with
    | .done proof => (⟨[record],.done ⟨proof,index+1⟩⟩,after)
    | .stop error => (⟨[record],.stop error⟩,after)
    | .retry =>
      let (rest,final) := run owner fuel (index+1) after
      (⟨record::rest.attempts,rest.result⟩,final)

theorem full_l1_erases {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (state : State) :
    (erase (run owner fuel index state).1,(run owner fuel index state).2) =
      SideChannelL1AttemptRecord.run (ownerL1 owner) fuel index state := by
  induction fuel generalizing index state with
  | zero => rfl
  | succ fuel ih =>
    unfold run SideChannelL1AttemptRecord.run ownerL1
    cases h : owner index state with
    | mk record after =>
      cases hr : record.l1.result with
      | done proof => simp only [hr]; rfl
      | stop error => simp only [hr]; rfl
      | retry =>
        simp only [hr]
        have tail := ih (index+1) after
        simp only [erase,List.map_cons] at tail ⊢
        cases hrest : run owner fuel (index+1) after with
        | mk rest final =>
          simp only [hrest] at tail ⊢
          unfold ownerL1 at tail
          rw [←tail]

theorem rejected_prefix {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (state after : State) (record : Attempt Proof)
    (step : owner index state = (record,after)) (reject : record.l1.result = .retry) :
    (run owner (fuel+1) index state).1.attempts =
      record::(run owner fuel (index+1) after).1.attempts := by
  simp only [run,step,reject]

theorem stopping_prefix {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (state after : State) (record : Attempt Proof) (error : ProverCommitRetry34.Error)
    (step : owner index state = (record,after)) (stop : record.l1.result = .stop error) :
    run owner (fuel+1) index state = (⟨[record],.stop error⟩,after) := by
  simp only [run,step,stop]

/-- The ROM list is flattened from every reached attempt, including rejected
attempts. This is a carrier projection, not a native history association. -/
def romHistory {Proof : Type} (r : Run Proof) := r.attempts.flatMap Attempt.rom

theorem rejected_rom_prefix {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (state after : State) (record : Attempt Proof)
    (step : owner index state = (record,after)) (reject : record.l1.result = .retry) :
    romHistory (run owner (fuel+1) index state).1 =
      record.rom ++ romHistory (run owner fuel (index+1) after).1 := by
  simp only [romHistory,rejected_prefix owner fuel index state after record step reject,
    List.flatMap_cons]

theorem l1_events {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (state : State) :
    SideChannelL1AttemptRecord.events (erase (run owner fuel index state).1) =
      SideChannelL1AttemptRecord.events
        (SideChannelL1AttemptRecord.run (ownerL1 owner) fuel index state).1 := by
  have h := congrArg Prod.fst (full_l1_erases owner fuel index state)
  exact congrArg SideChannelL1AttemptRecord.events h

#print axioms full_l1_erases
#print axioms rejected_prefix
#print axioms stopping_prefix
#print axioms rejected_rom_prefix
#print axioms l1_events
end R1Z.PV_L2_F3FullRetry
