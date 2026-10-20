import R1Z.ProverCommitSamplerComposition

/-! A symbolic factoring of the extracted reference loop body. No re-extraction,
new externals, or callback axioms are required. -/
set_option autoImplicit false
namespace R1Z.ProverCommitExtractedStep
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1ProverCommitReference
open R1Z.ProverCommitReferenceSource

/-- The extracted carried transition, retaining all monadic errors. -/
def step (hash : Hash) (domain : Slice U8) (s : State × Sample) : Result (State × Sample) := do
  match s.2 with
  | .Ok _ => ok s
  | .Err _ =>
    let (word, after) ← prover_commit_reference.next hash domain s.1
    let candidate ← lift (word &&& 2147483647#u32)
    let p ← aspis_core.field.P
    ok (after, if candidate < p then .Ok candidate else s.2)

theorem extracted_body (hash : Hash) (domain : Slice U8) (state : State)
    (attempts : I32) (result : Sample) (running : attempts < 16#i32) :
    prover_commit_reference.limb_loop.body hash domain state attempts result = (do
      let (after, sampled) ← step hash domain (state, result)
      ok (cont (after, I32.wrapping_add attempts 1#i32, sampled))) := by
  cases result with
  | Ok value =>
    simp only [prover_commit_reference.limb_loop.body, running, if_true,
      step, lift, bind_tc_ok]
  | Err error =>
    simp only [prover_commit_reference.limb_loop.body, running, if_true,
      step, lift, aspis_core.field.P, bind_assoc_eq, bind_tc_ok]
    cases h : prover_commit_reference.next hash domain state with
    | fail error => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨word, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      by_cases accepted : word &&& 2147483647#u32 < 2147483647#u32 <;>
        simp only [accepted, if_true, if_false, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]

theorem step_success (hash : Hash) (domain : Slice U8) (state : State) (a : U32) :
    step hash domain (state, .Ok a) = ok (state, .Ok a) := rfl

/-- Kleisli iteration composes source-step equalities including fail/div.
This is the monadic counterpart of the early-return composition theorem. -/
def iterate {S : Type} (body : S → Result S) : Nat → S → Result S
  | 0, s => ok s
  | n+1, s => do let t ← body s; iterate body n t

theorem iterate_refines {S : Type} (left right : S → Result S)
    (same : ∀ s, left s = right s) (n : Nat) (s : S) :
    iterate left n s = iterate right n s := by
  have e : left = right := funext same
  rw [e]

/-- A finite loop body with its remaining-tries rank made explicit. -/
def rankedBody {S : Type} (body : S → Result S) (x : S × Nat) :
    Result (ControlFlow (S × Nat) S) :=
  match x.2 with
  | 0 => ok (done x.1)
  | n+1 => do let t ← body x.1; ok (cont (t,n))

/-- Symbolic induction identifies a real Aeneas loop with finite composition. -/
theorem loop_eq_iterate {S : Type} (body : S → Result S) (n : Nat) (s : S) :
    loop (rankedBody body) (s,n) = iterate body n s := by
  induction n generalizing s with
  | zero => rw [loop]; rfl
  | succ n ih =>
    rw [loop]
    simp only [rankedBody, iterate]
    cases h : body s with
    | ok t => simpa only [bind_tc_ok] using ih t
    | fail error => rfl
    | div => rfl

theorem extracted_sixteen (hash : Hash) (domain : Slice U8)
    (left : State × Sample → Result (State × Sample))
    (same : ∀ s, left s = step hash domain s) (s : State × Sample) :
    loop (rankedBody left) (s,16) = iterate (step hash domain) 16 s := by
  rw [loop_eq_iterate]
  exact iterate_refines left (step hash domain) same 16 s

#print axioms extracted_body
#print axioms step_success
#print axioms iterate_refines
#print axioms loop_eq_iterate
#print axioms extracted_sixteen
end R1Z.ProverCommitExtractedStep
