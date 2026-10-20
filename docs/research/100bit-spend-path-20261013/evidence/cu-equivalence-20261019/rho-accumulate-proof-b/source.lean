import AspisR1RhoAccumulate.Funs
import CuSavingsRhoSourceBatch

set_option autoImplicit false
namespace AspisR1.CuSavingsRhoAccumulate
open Aeneas Aeneas.Std Result AspisR1RhoAccumulate
open CuSavingsRhoInitRow CuSavingsRhoVector CuSavingsRhoFinishModel
abbrev Acc := verifier.Accumulator
abbrev Prep := verifier.Prepared
abbrev BW := BatchedWeights

/-- Observe pending coefficients through the actual source materializer. -/
def materialize (out : Acc × Option BW) : Result Acc := do
  match out.2 with
  | none => .fail .panic
  | some pending =>
    let weights ← AspisR1CuRhoSource.verifier.BatchedWeights.finish pending out.1.weights
    .ok {out.1 with weights:=weights}

variable [AccumulateCommon]

/-- Entire source accumulation outcome, with no child-call success premise.
The unchanged RHS computations remain arbitrary common computations. -/
theorem source_equivalence (p : Prep) (a : Acc) (pending : BW)
    (node : U32) (value : aspis_core.field.WideExact)
    (hg : Good pending []) (hp : Canonical a.power)
    (hn : a.next.val ≤ 22) (hc : pending.terms.val < 22)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256)
    (hrows : a.weights.val.length=pending.raw.val.length) :
    factored_old.accumulate_with_node p {a with weights:=canonicalSlice pending} node value =
      (do let out ← factored_new.accumulate_with_node p a node value (some pending)
          materialize out) := by
  have hlen : alloc.vec.Vec.len a.weights=alloc.vec.Vec.len (canonicalSlice pending) := by
    apply UScalar.eq_of_val_eq
    simpa only [alloc.vec.Vec.len,Slice.len_val,Slice.length,canonicalSlice,List.length_map] using hrows
  have hl' : (alloc.vec.Vec.len (canonicalSlice pending)).val ≤ 256 := by rw [← hlen];exact hl
  unfold factored_old.accumulate_with_node factored_new.accumulate_with_node
  simp only [source_basis_old,source_basis_new,rho_old.coefficients,rho_new.coefficients]
  try dsimp only
  rw [hlen]
  cases hb : AspisR1RhoBasis.basis (alloc.vec.Vec.len (canonicalSlice pending)) node with
  | fail error => simp only [hb,bind_tc_fail]
  | div => simp only [hb,bind_tc_div]
  | ok basis =>
    obtain ⟨out,hbatch,hold,hcount,hlength,hgood⟩ :=
      CuSavingsRhoSourceBatch.source_batch pending a.power node basis a.next hg hp hn hl' hc hb
    have hnew := CuSavingsRhoOptimizedTraversal.source_eq_some a.weights pending a.power a.next basis hn hl
    rw [hlen] at hnew
    rw [hbatch] at hnew
    simp only [bind_tc_ok] at hnew
    have hfinish := CuSavingsRhoSourceFinish.source_success out a.weights
      (show a.weights.val.length=out.raw.val.length by rw [hrows,hlength])
    simp only [hb,bind_tc_ok,hold,hnew,uncurry_apply_pair]
    cases hm : WideExact.mul_qm31 value a.power with
    | fail error => simp only [hm,bind_tc_fail]
    | div => simp only [hm,bind_tc_div]
    | ok product =>
      simp only [hm,bind_tc_ok]
      cases ha : aspis_core.field.WideExact.add a.rhs product with
      | fail error => simp only [ha,bind_tc_fail]
      | div => simp only [ha,bind_tc_div]
      | ok rhs =>
        simp only [ha,bind_tc_ok,trace.value,AspisR1CuRho.trace.value]
        cases hq : aspis_core.field.QM31.mul a.power p.rho with
        | fail error => simp only [hq,bind_tc_fail]
        | div => simp only [hq,bind_tc_div]
        | ok power =>
          simp only [hq,bind_tc_ok]
          cases hn' : (a.next+1#usize : Result Usize) with
          | fail error => simp only [hn',bind_tc_fail]
          | div => simp only [hn',bind_tc_div]
          | ok next =>
            simp only [hn',bind_tc_ok,materialize,hfinish]

#print axioms materialize
#print axioms source_equivalence
end AspisR1.CuSavingsRhoAccumulate
