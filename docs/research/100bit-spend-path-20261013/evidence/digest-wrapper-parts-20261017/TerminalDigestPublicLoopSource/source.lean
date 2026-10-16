import AspisR1TerminalDigestBindingCandidate.Source
import EmptyRootSource
import AbsorptionGeneratedSlice
import Aeneas.Std
import Aeneas.Tactic.RustAttributes

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1TerminalDigestPublicLoop.Source
open AspisR1SelectedMaskProbe

/-- Exact outer loop from candidate Funs source lines 657–678, except its two
binding calls target the already isolated exact source slice.  This remains a
candidate-source replay slice; release-caller correspondence is separate. -/
@[rust_loop]
def public_digest_lanes_loop
  (iter : core.ops.range.Range Std.Usize) (a : Array field.QM31 16#usize)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
  (digests : Array field.QM31 8#usize)
  (source : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
  Result ((Array field.QM31 8#usize) ×
    pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (digests, source)
  | some level =>
    let block ← 34#usize + level
    let i ← source.next_pair_index >>> level
    let i1 ← lift (i &&& 1#u64)
    if i1 = 0#u64 then
      let i2 ← block * 16#usize
      let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i2
      let a1 ← AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
      let digests1 ← AspisR1TerminalDigestBindingCandidate.add_digest_binding
        digests q a AspisR1AbsorptionCandidate.poseidon2.RATE a1 true
      public_digest_lanes_loop iter1 a selectors digests1 source
    else
      let i2 ← block * 16#usize
      let i3 ← i2 + 12#usize
      let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
      let a1 ← Array.index_usize source.frontier level
      let digests1 ← AspisR1TerminalDigestBindingCandidate.add_digest_binding
        digests q a 0#usize a1 false
      public_digest_lanes_loop iter1 a selectors digests1 source
partial_fixpoint
end AspisR1TerminalDigestPublicLoop.Source
