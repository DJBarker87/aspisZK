import CuSavingsRhoFinishLoop

/-! Complete emitted finish method under the concrete mutable-enumerate
interface. Only the original length admission is required for successful
indexing; no assumption is made about raw-limb canonicality or old outputs.
The runtime/source binding and enclosing verifier remain separate obligations. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoFinish
open Aeneas Aeneas.Std Result
open AspisR1CuRho
open AspisR1.CuSavingsRhoFinishModel

theorem source_success (self : verifier.BatchedWeights) (weights : Slice field.QM31)
    (hlen : weights.val.length = self.raw.val.length) :
    verifier.BatchedWeights.finish self weights = .ok (canonicalSlice self) := by
  let iter : Enum := {iter := {slice := weights},count := 0#usize}
  have hlen' : iter.iter.slice.val.length = (canonicalSlice self).val.length := by
    simpa only [iter,canonicalSlice,List.length_map] using hlen
  have hr := CuSavingsRhoFinishLoop.source_success iter self hlen' (by
    change 0 ≤ weights.val.length
    omega) (by rfl)
  unfold verifier.BatchedWeights.finish
  simp only [Aeneas.Std.core.slice.Slice.iter_mut,
    AspisR1CuRho.core.iter.traits.iterator.Iterator.enumerate.trait_default,bind_tc_ok]
  change (do
    let out ← verifier.BatchedWeights.finish_loop iter (fun out => out) self
    .ok out.iter.slice) = _
  rw [hr]
  apply congrArg Result.ok
  apply Subtype.ext
  rfl

#print axioms source_success
end AspisR1.CuSavingsRhoFinish
