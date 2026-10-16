import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import OccupancyGeneratedSlice

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
noncomputable section

namespace AspisR1TerminalDigestBindingCandidate
open AspisR1SelectedMaskProbe

/-- Exact source literal from terminal indexed candidate Funs SHA
`04fc129bbd54c8792d5c11e6c017e810cfc68d7a4a9577eca9455088ed04a42e`;
only namespaced locally to share `OccupancyGeneratedSlice` carriers. -/
@[global_simps, irreducible]
def poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK : field.M31 := 1095962629#u32

/-- Exact source body slice for production `add_digest_binding`, from the
sealed indexed candidate Funs (SHA above), lines 3161–3211. -/
@[rust_loop]
def add_digest_binding_loop
  (iter : core.ops.range.Range Std.Usize) (output : Array field.QM31 8#usize)
  (selector : field.QM31) (opened : Array field.QM31 16#usize)
  (start : Std.Usize) (expected : Array field.M31 8#usize) (right_tweak : Bool)
  : Result (Array field.QM31 8#usize) := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok output
  | some lane =>
    let target ← Array.index_usize expected lane
    let (iter2, target1) ←
      if right_tweak then do
        let i ← lane + 1#usize
        let m ← if i = poseidon2.DIGEST_ELEMS
          then field.M31.add target poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK
          else ok target
        ok (iter1, m)
      else ok (iter1, target)
    let q ← Array.index_usize output lane
    let i ← start + lane
    let q1 ← Array.index_usize opened i
    let q2 ← pool_v1.pair_forest_semantic_terminal.lift_m31 target1
    let q3 ← field.QM31.sub q1 q2
    let q4 ← field.QM31.mul selector q3
    let q5 ← field.QM31.add q q4
    let a ← Array.update output lane q5
    add_digest_binding_loop iter2 a selector opened start expected right_tweak
partial_fixpoint

/-- Checked wrapper from the source helper: initializes the inclusive/exclusive
range `[0, DIGEST_ELEMS)` and invokes the literal lane loop. -/
@[reducible]
def add_digest_binding
  (output : Array field.QM31 8#usize) (selector : field.QM31)
  (opened : Array field.QM31 16#usize) (start : Std.Usize)
  (expected : Array field.M31 8#usize) (right_tweak : Bool) :
  Result (Array field.QM31 8#usize) := do
  add_digest_binding_loop
    { start := 0#usize, «end» := poseidon2.DIGEST_ELEMS }
    output selector opened start expected right_tweak

end AspisR1TerminalDigestBindingCandidate
end
