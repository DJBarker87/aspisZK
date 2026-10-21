import R1Z.ProverCommitOwnedCollection
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedCollection
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R1Z.ProverCommitStepLoop (State Hash)
open R1Z.ProverCommitFourSteps (collect)
abbrev SampleList := core.result.Result (List U32) state_only_hiding.StateOnlyMaskBuildError

def erase (run : Result (Status × Values × State)) : Result (SampleList × State) := do
  let (status, values, state) ← run
  match status with
  | .Err e => ok (.Err e, state)
  | .Ok () => ok (.Ok values.val, state)

def prepend (values : List U32) (run : Result (SampleList × State)) : Result (SampleList × State) := do
  let (sample, state) ← run
  match sample with
  | .Err e => ok (.Err e, state)
  | .Ok tail => ok (.Ok (values ++ tail), state)

/-- The owned Rust accumulator implements precisely the existing sequential
collect, in ascending sample order. Capacity is checked symbolically. -/
theorem finite_collect (hash : Hash) (domain : Slice U8) (n : Nat)
    (values : Values) (state : State) (room : values.val.length + n ≤ Usize.max) :
    erase (finite hash domain n values state) =
      prepend values.val (collect (prover_commit_reference.limb_caller hash domain) n state) := by
  induction n generalizing values state with
  | zero => simp only [finite, erase, collect, prepend, bind_tc_ok, Aeneas.Std.uncurry_apply_pair, List.append_nil]
  | succ n ih =>
    simp only [finite, collect]
    cases hs : prover_commit_reference.limb_caller hash domain state with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      cases sample with
      | Err e => rfl
      | Ok value =>
        obtain ⟨values', pushed, contents⟩ := WP.spec_imp_exists
          (alloc.vec.Vec.push_spec values value (by omega))
        simp only [pushed, bind_tc_ok]
        rw [ih values' after (by rw [contents, List.length_append]; simp only [List.length_singleton]; omega)]
        rw [contents]
        unfold prepend
        cases ht : collect (prover_commit_reference.limb_caller hash domain) n after with
        | fail e => rfl
        | div => rfl
        | ok pair =>
          rcases pair with ⟨tail, final⟩
          simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
          cases tail with
          | Err e => rfl
          | Ok tail => simp only [List.append_assoc, List.singleton_append, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]

/-- The scalar producer used by the fixed decoder is the extracted owned Rust
function, not a separately assumed aggregate sampler. -/
theorem extracted_collect (hash : Hash) (domain : Slice U8) (remaining : Usize)
    (values : Values) (state : State)
    (room : values.val.length + remaining.val ≤ Usize.max) :
    erase (prover_commit_reference.collect_m31_owned hash domain state remaining values) =
      prepend values.val (collect (prover_commit_reference.limb_caller hash domain) remaining.val state) := by
  rw [extracted_finite hash domain remaining.val remaining values state rfl]
  exact finite_collect hash domain remaining.val values state room

#print axioms finite_collect
#print axioms extracted_collect
end R1Z.ProverCommitOwnedCollection
