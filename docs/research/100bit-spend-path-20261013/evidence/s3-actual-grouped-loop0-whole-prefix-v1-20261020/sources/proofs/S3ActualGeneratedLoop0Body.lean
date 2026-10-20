import AspisR1GroupedPairActualFieldOpsV3.Funs
import Aeneas.Std.RangeIter
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1GroupedPairActualFieldOpsV3

private theorem let_pair_mk {A B C : Type} (a : A) (b : B) (k : A → B → C) :
    (let (x, y) := (a, b); k x y) = k a b := rfl

theorem generated_loop0_body_success
    (ops : Operations)
    (bytes : Slice Std.U8)
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
    (hfield : ops.decodeField bytes j = .ok inputCoeff)
    (hadd : ops.add oldCoeff inputCoeff = .ok newCoeff)
    (hupdate : Array.update coefficients group newCoeff = .ok updated) :
    weights.s2_grouped_inactive_pair_loop0.body ops bytes iter coefficients =
      ok (cont (iterNext, updated)) := by
  rw [weights.s2_grouped_inactive_pair_loop0.body, hnext]
  change (match some j with
    | none => ok (done coefficients)
    | some j => do
        let i ← Array.index_usize weights.S2_INACTIVE_GROUPS j
        let group ← lift (UScalar.cast .Usize i)
        let we ← Array.index_usize coefficients group
        let we1 ← ops.decodeField bytes j
        let we2 ← ops.add we we1
        let a ← Array.update coefficients group we2
        ok (cont (iterNext, a))) = ok (cont (iterNext, updated))
  simp only [bind_tc_ok, hgroup, hcast, hold, hfield, hadd, hupdate]

end AspisR1GroupedPairActualFieldOpsV3

#print axioms AspisR1GroupedPairActualFieldOpsV3.generated_loop0_body_success
