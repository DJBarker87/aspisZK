import R1Z.ProverCommitOwnedCache
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R1Z.ProverCommitStepLoop (State Hash scalarFinite)
open R1Z.ProverCommitFourSteps (collect)
open R1Z.ProverCommitSequentialFibres
open R1Z.ProverCommitWordCarrier
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

def erase (run : Result (core.result.Result (List U32) R1Z.ProverCommitFourSteps.Error × State)) : Option (List F) :=
  match run with
  | ok (.Ok values, _) => some (values.map fieldValue)
  | _ => none

def sequence (hash : Hash) (domain : Slice U8) : Nat → Nat → State → Option (List F)
  | 0, _, _ => some []
  | L+1, r, state =>
    match scalarFinite hash domain r state with
    | ok (.Ok value, after) => (sequence hash domain L 16 after).map (fieldValue value :: ·)
    | _ => none

theorem sequence_collect (hash : Hash) (domain : Slice U8) (L : Nat) (state : State) :
    sequence (K := K) hash domain L 16 state =
      erase (collect (prover_commit_reference.limb_caller hash domain) L state) := by
  induction L generalizing state with
  | zero => rfl
  | succ L ih =>
    rw [sequence, collect]
    have caller : prover_commit_reference.limb_caller hash domain state =
        scalarFinite hash domain 16 state := R1Z.ProverCommitStepLoop.caller_sixteen hash domain state
    rw [caller]
    cases hs : scalarFinite hash domain 16 state with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      cases sample with
      | Err e => rfl
      | Ok value =>
        simp only [ih]
        cases ht : collect (prover_commit_reference.limb_caller hash domain) L after with
        | fail e => rfl
        | div => rfl
        | ok pair =>
          rcases pair with ⟨tail, final⟩
          cases tail <;> rfl

theorem sequence_zero (hash : Hash) (domain : Slice U8) (L : Nat) (state : State) :
    sequence (K := K) hash domain (L+1) 0 state = none := rfl

theorem sequence_step (hash : Hash) (domain : Slice U8) (L r : Nat) (state : State) :
    sequence (K := K) hash domain (L+1) (r+1) state =
      match prover_commit_reference.next hash domain state with
      | ok (word, after) =>
        if word &&& 2147483647#u32 < aspis_core.field.P then
          (sequence hash domain L 16 after).map (fieldValue (word &&& 2147483647#u32) :: ·)
        else sequence hash domain (L+1) r after
      | _ => none := by
  simp only [sequence, R1Z.ProverCommitStepLoop.scalarFinite_succ]
  cases hn : prover_commit_reference.next hash domain state with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨word, after⟩
    simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
    split_ifs <;> rfl

def valuesList {A : Type} : (L : Nat) → Values A L → List A
  | 0, _ => []
  | L+1, v => v.1 :: valuesList L v.2

theorem decode_list_step {W A : Type} [Fintype W] (d : W → Option A)
    (n L r : Nat) (ws : Fin (n+1) → W) :
    (decodeWords d (n+1) (L+1) (r+1) ws).map (valuesList (L+1)) =
      match d (ws 0) with
      | none => (decodeWords d n (L+1) r (fun j => ws j.succ)).map (valuesList (L+1))
      | some a => ((decodeWords d n L 16 (fun j => ws j.succ)).map (valuesList L)).map (a :: ·) := by
  simp only [decodeWords, step]
  cases hd : d (ws 0) with
  | none => rfl
  | some a =>
    cases ht : decodeWords d n L 16 (fun j => ws j.succ) <;> rfl

#print axioms sequence_collect
#print axioms sequence_zero
#print axioms sequence_step
#print axioms decode_list_step
end R1Z.ProverCommitOwnedDecoder
