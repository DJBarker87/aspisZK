import DigestFixedPrefix

/-! Exact initial straight-line cut of the sealed candidate public_digest_lanes.
The sole source-body renaming is the already-proved binding helper owner. -/
set_option autoImplicit false
namespace AspisR1.DigestFixedPrefix.Source
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

/-- Exact source cut; the enclosing loop and suffix are deliberately excluded. -/
def exactPrefix
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
    Result (Array field.QM31 8#usize) := do
  let digests := Array.repeat 8#usize field.QM31.ZERO
  let i ← 56#usize * 16#usize
  let i1 ← i + 11#usize
  let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i1
  let digests1 ←
    AspisR1TerminalDigestBindingCandidate.add_digest_binding digests q
      openings.z 0#usize public1.anchor false
  let i2 ← 26#usize * 16#usize
  let i3 ← i2 + 11#usize
  let q1 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
  let digests2 ←
    AspisR1TerminalDigestBindingCandidate.add_digest_binding digests1 q1
      openings.z 0#usize public1.nullifier false
  let digests3 ←
    match public1.recipient with
    | none => ok digests2
    | some recipient =>
      do
      let i4 ← 29#usize * 16#usize
      let i5 ← i4 + 11#usize
      let q2 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i5
      AspisR1TerminalDigestBindingCandidate.add_digest_binding digests2 q2
        openings.z 0#usize recipient false
  let i4 ← 32#usize * 16#usize
  let i5 ← i4 + 11#usize
  let q2 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i5
  let digests4 ←
    AspisR1TerminalDigestBindingCandidate.add_digest_binding digests3 q2
      openings.z 0#usize public1.change false
  ok digests4

private theorem result_right_identity {α : Type} (x : Result α) :
    (do let y ← x; Result.ok y) = x := by
  cases x <;> rfl

/-- Factoring the repeated fragment does not change prefix execution or errors. -/
theorem exactPrefix_eq_factored
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
    exactPrefix public1 openings selectors =
      AspisR1.DigestFixedPrefix.fixedPrefix public1 openings.z selectors := by
  simp only [exactPrefix, AspisR1.DigestFixedPrefix.fixedPrefix,
    AspisR1.DigestFixedBinding.bindBlock, AspisR1.DigestFixedPrefix.zero, bind_assoc_eq,
    bind_tc_ok, result_right_identity]
  all_goals rfl

#print axioms exactPrefix_eq_factored
end AspisR1.DigestFixedPrefix.Source
