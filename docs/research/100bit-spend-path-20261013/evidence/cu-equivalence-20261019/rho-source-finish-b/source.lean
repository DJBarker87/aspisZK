import CuSavingsRhoSourceFinishLoop
import CuSavingsRhoFinish

/-! Whole finish equivalence at the matching-length caller invariant, using
the unchanged emitted standard next body rather than merely its local model.
Allocation/initialization and enclosing verifier admission remain required. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoSourceFinish
open Aeneas Aeneas.Std Result
open AspisR1CuRho
open CuSavingsRhoFinishModel

theorem source_success (self : verifier.BatchedWeights) (weights : Slice field.QM31)
    (hlen : weights.val.length = self.raw.val.length) :
    AspisR1CuRhoSource.verifier.BatchedWeights.finish self weights = .ok (canonicalSlice self) := by
  let iter : Enum := {iter := {slice := weights},count := 0#usize}
  have hlen' : iter.iter.slice.val.length = (canonicalSlice self).val.length := by
    simpa only [iter,canonicalSlice,List.length_map] using hlen
  obtain ⟨last,hrun,hiter⟩ := CuSavingsRhoSourceFinishLoop.source_success iter self hlen' (by
    change 0 ≤ weights.val.length
    omega) (by rfl)
  unfold AspisR1CuRhoSource.verifier.BatchedWeights.finish
  simp only [Aeneas.Std.core.slice.Slice.iter_mut,
    AspisR1CuRhoSource.core.iter.traits.iterator.Iterator.enumerate.trait_default,
    AspisR1CuRho.core.iter.traits.iterator.Iterator.enumerate.trait_default,bind_tc_ok]
  change (do
    let out ← AspisR1CuRhoSource.verifier.BatchedWeights.finish_loop iter (fun out => out) self
    .ok out.iter.slice) = _
  rw [hrun]
  apply congrArg Result.ok
  change last.iter.slice = canonicalSlice self
  calc
    last.iter.slice = (modelIter iter (canonicalSlice self) hlen').iter.slice :=
      congrArg (fun it : Iter => it.slice) hiter
    _ = canonicalSlice self := by apply Subtype.ext;rfl

theorem source_eq_model (self : verifier.BatchedWeights) (weights : Slice field.QM31)
    (hlen : weights.val.length = self.raw.val.length) :
    AspisR1CuRhoSource.verifier.BatchedWeights.finish self weights =
      AspisR1CuRho.verifier.BatchedWeights.finish self weights := by
  rw [source_success self weights hlen,CuSavingsRhoFinish.source_success self weights hlen]

#print axioms source_success
#print axioms source_eq_model
end AspisR1.CuSavingsRhoSourceFinish
