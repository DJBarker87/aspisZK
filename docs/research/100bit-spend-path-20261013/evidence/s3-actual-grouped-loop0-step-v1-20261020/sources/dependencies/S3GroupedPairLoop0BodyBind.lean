import AspisR1GroupedPairCut.Funs
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1GroupedPairCut.Proofs

/-- Exact bind-threading equation for one successful generated coefficient
accumulation iteration. The premises expose each checked operation so callers
can discharge them with the corresponding Aeneas operation specifications. -/
theorem grouped_pair_loop0_body_success
    (ops : weights.WideExactOps)
    (coeff : Array field.WideExact 64#usize)
    (iter : core.ops.range.Range Std.Usize)
    (coefficients : Array field.WideExact 12#usize)
    (j : Std.Usize) (iterNext : core.ops.range.Range Std.Usize)
    (groupByte : Std.U8) (group : Std.Usize)
    (oldCoeff inputCoeff newCoeff : field.WideExact)
    (updated : Array field.WideExact 12#usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some j, iterNext))
    (hgroup : Array.index_usize weights.S2_INACTIVE_GROUPS j = .ok groupByte)
    (hcast : lift (UScalar.cast .Usize groupByte) = .ok group)
    (hold : Array.index_usize coefficients group = .ok oldCoeff)
    (hin : Array.index_usize coeff j = .ok inputCoeff)
    (hadd : ops.add oldCoeff inputCoeff = .ok newCoeff)
    (hupdate : Array.update coefficients group newCoeff = .ok updated) :
    weights.s2_grouped_inactive_pair_loop0.body ops coeff iter coefficients =
      .ok (.cont (iterNext, updated)) := by
  rw [weights.s2_grouped_inactive_pair_loop0.body, hnext]
  change (match some j with
    | none => ok (done coefficients)
    | some j => do
        let i ← Array.index_usize weights.S2_INACTIVE_GROUPS j
        let group ← lift (UScalar.cast .Usize i)
        let we ← Array.index_usize coefficients group
        let we1 ← Array.index_usize coeff j
        let we2 ← ops.add we we1
        let a ← Array.update coefficients group we2
        ok (cont (iterNext, a))) = ok (.cont (iterNext, updated))
  simp only [bind_tc_ok, hgroup, hcast, hold, hin, hadd, hupdate]

end AspisR1GroupedPairCut.Proofs
#print axioms AspisR1GroupedPairCut.Proofs.grouped_pair_loop0_body_success
