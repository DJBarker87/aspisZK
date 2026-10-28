import R1Z.SideChannelL1AttemptRecord
set_option autoImplicit false
namespace PV_L1_NativeProducer
open R1Z R1Z.SideChannelL1AttemptRecord
open ProverCommitRetry34

/-- The native retry owner has two distinct Result boundaries. The callback
error escapes `?`; only an error from the prover enters the retry match.
Each leaf supplies its complete ordered prefix and updated state. -/
abbrev Callback (S Secret : Type) := Nat → S →
  (List Event × Except Error Secret) × S
abbrev Prover (S Secret Proof : Type) := Secret → S →
  (List Event × Except Error Proof) × S

def classifyResult {Proof : Type} : Except Error Proof → Step Proof
  | .ok p => .done p
  | .error .Rejected => .retry
  | .error e => .stop e

def producer {S Secret Proof : Type} (callback : Callback S Secret)
    (prover : Prover S Secret Proof) : Owner S Proof := fun index state =>
  let ((before,out),after) := callback index state
  match out with
  | .error e => (⟨before,.stop e⟩,after)
  | .ok secret =>
    let ((suffix,result),final) := prover secret after
    (⟨before ++ suffix,classifyResult result⟩,final)

/-- Control interpretation of native retry_attempt, with its distinct callback
and prover arms. This definition retains all prefixes even when a later call
fails. Native leaf-event association is a separate, open obligation. -/
def native {S Secret Proof : Type} (callback : Callback S Secret)
    (prover : Prover S Secret Proof) : Nat → Nat → S → Run Proof × S
  | 0, _, s => (⟨[],.stop .AttemptsExhausted⟩,s)
  | fuel+1, index, s =>
    let ((before,out),after) := callback index s
    match out with
    | .error e => (⟨[⟨before,.stop e⟩],.stop e⟩,after)
    | .ok secret =>
      let ((suffix,result),final) := prover secret after
      let record : Attempt Proof := ⟨before ++ suffix,classifyResult result⟩
      match result with
      | .ok proof => (⟨[record],.done ⟨proof,index+1⟩⟩,final)
      | .error .Rejected =>
        let (rest,finish) := native callback prover fuel (index+1) final
        (⟨record::rest.attempts,rest.result⟩,finish)
      | .error e => (⟨[record],.stop e⟩,final)

theorem native_eq_model {S Secret Proof : Type} (callback : Callback S Secret)
    (prover : Prover S Secret Proof) (fuel index : Nat) (state : S) :
    native callback prover fuel index state =
      run (producer callback prover) fuel index state := by
  induction fuel generalizing index state with
  | zero => rfl
  | succ fuel ih =>
    simp only [native,run,producer]
    cases h : callback index state with
    | mk pair after =>
      rcases pair with ⟨before,out⟩
      cases out with
      | error e => rfl
      | ok secret =>
        cases hp : prover secret after with
        | mk pair final =>
          rcases pair with ⟨suffix,result⟩
          cases result with
          | ok proof => rfl
          | error e =>
            cases e <;> simp only [classifyResult]
            all_goals first | rfl | rw [ih]
#print axioms native_eq_model
end PV_L1_NativeProducer
