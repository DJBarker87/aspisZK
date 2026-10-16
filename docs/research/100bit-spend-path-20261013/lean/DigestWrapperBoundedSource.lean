import TerminalDigestPublicLoopSource
import BoundedControlSource

/-! Bounded-carry implementation candidate for the public_digest_lanes wrapper.
This explicit model edit follows the reviewable Rust patch; correspondence to
a full re-extraction and release artifact is a separate open obligation. -/
open Aeneas Aeneas.Std Result
namespace AspisR1DigestWrapperBoundedCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::public_digest_lanes]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 614:0-699:1 -/
def pool_v1.pair_forest_semantic_terminal.public_digest_lanes
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 8#usize)
  := do
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
  let (digests5, source) ←
    AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop
      { start := 0#usize, «end» := 20#usize } openings.z selectors digests4
      public1.transition.live_snapshot
  let i6 ← 53#usize * 16#usize
  let i7 ← i6 + 11#usize
  let q3 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i7
  let digests6 ←
    AspisR1TerminalDigestBindingCandidate.add_digest_binding digests5 q3
      openings.z 0#usize public1.transition.candidate_afterstate.next_root
      false
  let carry ← AspisBoundedControl.bounded_carry source.next_pair_index
  if carry < 20#usize
  then
    let i10 ← 33#usize + carry
    let i11 ← i10 * 16#usize
    let i12 ← i11 + 11#usize
    let q4 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i12
    let a ←
      Array.index_usize public1.transition.candidate_afterstate.next_frontier
        carry
    AspisR1TerminalDigestBindingCandidate.add_digest_binding digests6 q4
      openings.z 0#usize a false
  else ok digests6

end AspisR1DigestWrapperBoundedCandidate
