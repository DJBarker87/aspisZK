import R1Z.ProverCommitMaterialPrefix
/-! Explicit monadic case splits connect the extracted owned collectors to
arbitrary-prefix algebra. Scalar loops remain symbolic named callees. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaterialTransport16
open Aeneas Aeneas.Std Result AspisR1ProverMaterial14
open R1Z.ProverCommitMaterialRecursion (Hash State Values QValues)
open R1Z.ProverCommitMaterialPrefix

theorem m31_accumulate (hash : Hash) (domain : Slice U8) (n : Nat)
    (values : Values) (state : State) :
    ProverCommitMaterialRecursion.finite hash domain n values state =
      accumulate (prover_commit_reference.limb_caller hash domain) n values state := by
  induction n generalizing values state with
  | zero => rfl
  | succ n ih =>
    simp only [ProverCommitMaterialRecursion.finite, accumulate]
    cases hs : prover_commit_reference.limb_caller hash domain state with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      cases sample with
      | Err e => rfl
      | Ok value =>
        dsimp only
        cases hp : alloc.vec.Vec.push values value with
        | fail e => simp only [hp, bind_tc_fail]
        | div => simp only [hp, bind_tc_div]
        | ok fresh =>
          simp only [hp, bind_tc_ok, lift]
          exact ih fresh after

/-- Arbitrary existing prefix, arbitrary remaining length within Usize
capacity; errors and final state agree with the extracted owned reference. -/
theorem m31_extracted_prefix (hash : Hash) (domain : Slice U8) (n : Nat)
    (remaining : Usize) (values : Values) (state : State)
    (count : remaining.val = n) (room : values.val.length + n ≤ Usize.max) :
    erase (prover_commit_reference.collect_m31_owned hash domain state remaining values) =
      prepend values.val (collect (prover_commit_reference.limb_caller hash domain) n state) := by
  rw [ProverCommitMaterialRecursion.extracted_finite hash domain n remaining values state count,
    m31_accumulate]
  exact arbitrary_prefix _ n values state room

#print axioms m31_accumulate
#print axioms m31_extracted_prefix

theorem qm31_accumulate (hash : Hash) (domain : Slice U8) (n : Nat)
    (values : QValues) (state : State) :
    ProverCommitMaterialRecursion.qmFinite hash domain n values state =
      accumulate (prover_commit_reference.qm31_caller hash domain) n values state := by
  induction n generalizing values state with
  | zero => rfl
  | succ n ih =>
    simp only [ProverCommitMaterialRecursion.qmFinite, accumulate]
    cases hs : prover_commit_reference.qm31_caller hash domain state with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨sample, after⟩
      simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      cases sample with
      | Err e => rfl
      | Ok value =>
        dsimp only
        cases hp : alloc.vec.Vec.push values value with
        | fail e => simp only [hp, bind_tc_fail]
        | div => simp only [hp, bind_tc_div]
        | ok fresh =>
          simp only [hp, bind_tc_ok, lift]
          exact ih fresh after

/-- Arbitrary existing prefix, arbitrary remaining length within Usize
capacity; errors and final state agree with the extracted owned reference. -/
theorem qm31_extracted_prefix (hash : Hash) (domain : Slice U8) (n : Nat)
    (remaining : Usize) (values : QValues) (state : State)
    (count : remaining.val = n) (room : values.val.length + n ≤ Usize.max) :
    erase (prover_commit_reference.collect_qm31_owned hash domain state remaining values) =
      prepend values.val (collect (prover_commit_reference.qm31_caller hash domain) n state) := by
  rw [ProverCommitMaterialRecursion.qm_extracted_finite hash domain n remaining values state count,
    qm31_accumulate]
  exact arbitrary_prefix _ n values state room

#print axioms qm31_accumulate
#print axioms qm31_extracted_prefix
end R1Z.ProverCommitMaterialTransport16
