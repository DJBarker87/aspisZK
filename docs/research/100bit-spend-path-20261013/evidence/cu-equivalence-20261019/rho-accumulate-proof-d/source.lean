import AspisR1RhoAccumulate.Funs
import CuSavingsRhoSourceBatch
import CuSavingsRhoPowerTail

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
    simp only [hlen] at hnew
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

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- Derive the next invariant from a successful whole source call, rather than
assuming any child call succeeded or supplied a canonical value. -/
theorem source_preserves (p : Prep) (a : Acc) (pending : BW)
    (node : U32) (value : aspis_core.field.WideExact)
    (hg : Good pending []) (hp : Canonical a.power) (hr : Canonical p.rho)
    (hn : a.next.val < 22) (hc : pending.terms.val < 22)
    (hl : (alloc.vec.Vec.len a.weights).val ≤ 256)
    (hrows : a.weights.val.length=pending.raw.val.length)
    (result : Acc × Option BW)
    (h : factored_new.accumulate_with_node p a node value (some pending) = .ok result) :
    ∃ out : BW,result.2=some out ∧ Good out [] ∧
      out.terms.val=pending.terms.val+1 ∧ out.raw.val.length=pending.raw.val.length ∧
      result.1.weights=a.weights ∧ Canonical result.1.power ∧
      result.1.next.val=a.next.val+1 ∧ result.1.next.val ≤ 22 := by
  have hlen : alloc.vec.Vec.len a.weights=alloc.vec.Vec.len (canonicalSlice pending) := by
    apply UScalar.eq_of_val_eq
    simpa only [alloc.vec.Vec.len,Slice.len_val,Slice.length,canonicalSlice,List.length_map] using hrows
  have hl' : (alloc.vec.Vec.len (canonicalSlice pending)).val ≤ 256 := by rw [← hlen];exact hl
  unfold factored_new.accumulate_with_node at h
  obtain ⟨basis,hbasis,h⟩ := bind_ok _ _ _ h
  change AspisR1RhoBasis.basis (alloc.vec.Vec.len a.weights) node = .ok basis at hbasis
  rw [hlen] at hbasis
  obtain ⟨out,hbatch,_,hcount,hlength,hgood⟩ :=
    CuSavingsRhoSourceBatch.source_batch pending a.power node basis a.next hg hp (by omega) hl' hc hbasis
  have hnew := CuSavingsRhoOptimizedTraversal.source_eq_some a.weights pending a.power a.next basis (by omega) hl
  simp only [hlen] at hnew
  rw [hbatch] at hnew
  simp only [bind_tc_ok] at hnew
  simp only [rho_new.coefficients,hnew,bind_tc_ok,uncurry_apply_pair] at h
  obtain ⟨product,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨rhs,_,h⟩ := bind_ok _ _ _ h
  simp only [trace.value,AspisR1CuRho.trace.value,bind_tc_ok] at h
  obtain ⟨q,hq,hcanonical,_⟩ := ExtractedCurrentQM31Mul.current_qm_mul_words
    (CuSavingsRhoReference.toCurrent a.power) (CuSavingsRhoReference.toCurrent p.rho) hp hr
  have hmul : aspis_core.field.QM31.mul a.power p.rho =
      .ok (CuSavingsRhoReference.fromCurrent q) := by
    simp only [aspis_core.field.QM31.mul,hq,bind_tc_ok]
  obtain ⟨next,hadd,hval⟩ := CuSavingsRhoPowerTail.next_success a.next hn
  simp only [hmul,hadd,bind_tc_ok] at h
  cases Result.ok.inj h
  refine ⟨out,rfl,hgood,hcount,hlength,rfl,?_,hval,?_⟩
  · exact hcanonical
  · omega

#print axioms source_preserves
#print axioms materialize
#print axioms source_equivalence
end AspisR1.CuSavingsRhoAccumulate
