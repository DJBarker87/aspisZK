import FIy_DigestBinding
import FIy_ArraySlot
import FIw_SelectorRow
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_FrontierStep
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Snapshot := pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

def run (level : Usize) (a : Array NQ 16#usize) (selectors : Selectors)
    (digests : Array NQ 8#usize) (source : Snapshot) : Result (Array NQ 8#usize) := do
  let block ← 34#usize + level
  let i ← source.next_pair_index >>> level
  let i1 ← lift (i &&& 1#u64)
  if i1 = 0#u64
  then
    let i2 ← block * 16#usize
    let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i2
    let a1 ← pool_v1.pair_forest_semantic_terminal.empty_root level
    let digests1 ←
      pool_v1.pair_forest_semantic_terminal.add_digest_binding digests q a
        poseidon2.RATE a1 true
    ok digests1
  else
    let i2 ← block * 16#usize
    let i3 ← i2 + 12#usize
    let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
    let a1 ← Array.index_usize source.frontier level
    let digests1 ←
      pool_v1.pair_forest_semantic_terminal.add_digest_binding digests q a
        0#usize a1 false
    ok digests1

end AspisR1.FIy_FrontierStep
end
