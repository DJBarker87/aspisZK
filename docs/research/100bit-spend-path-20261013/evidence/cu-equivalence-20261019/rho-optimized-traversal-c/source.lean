import AspisR1RhoOptimizedLoop.Funs
import CuSavingsRhoSourceOption
import CuSavingsRhoReferenceTraversal

set_option autoImplicit false
namespace AspisR1.CuSavingsRhoOptimizedTraversal
open Aeneas Aeneas.Std Result ControlFlow AspisR1CuRho
open CuSavingsRhoReference CuSavingsRhoVector CuSavingsRhoReferenceLoop CuSavingsRhoPushStep
open CuSavingsRangeTraversal CuSavingsRhoRangeInputs
abbrev Rows := alloc.vec.Vec AspisR1RhoCoefficients.aspis_core.field.QM31
abbrev Range := core.ops.range.Range Usize
abbrev Basis := Array U32 256#usize
abbrev BW := verifier.BatchedWeights
abbrev Source := AspisR1RhoCoefficients.rho_new.coefficients_loop.body
abbrev sourceLoop := AspisR1RhoCoefficients.rho_new.coefficients_loop

theorem source_body (power : field.QM31) (next : Usize) (basis : Basis)
    (iter after : Range) (index : Usize) (rows : Rows) (self : BW)
    (back : Option BW → Option BW)
    (hn : next.val ≤ 22) (hl : rows.val.length ≤ 256)
    (hi : index.val < rows.val.length)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some index,after)) :
    Source power next basis iter back rows (some self) = (do
      let out ← verifier.BatchedWeights.push self index power
        (basis.val[index.val]'(by
          have hi' : index.val < 256 := Nat.lt_of_lt_of_le hi hl
          simpa only [basis.property,show (256#usize).val=256 by scalar_tac] using hi'))
      .ok (.cont (after,back,rows,some out))) := by
  have hb : index.val < basis.val.length := by
    have hi' : index.val < 256 := Nat.lt_of_lt_of_le hi hl
    simpa only [basis.property,show (256#usize).val=256 by scalar_tac] using hi'
  let b := basis.val[index.val]'hb
  rw [Source,AspisR1RhoCoefficients.rho_new.coefficients_loop.body,hnext]
  simp only [bind_tc_ok,uncurry_apply_pair,AspisR1RhoSourceOption.source_reborrow,
    array_read basis index hb,AspisR1RhoCoefficients.BatchedWeights.push]
  cases hs : verifier.BatchedWeights.push self index power b with
  | fail error => simp only [hs,bind_tc_fail]
  | div => simp only [hs,bind_tc_div]
  | ok out =>
    simp only [hs,bind_tc_ok]
    obtain ⟨productIndex,ix,hprod,hadd⟩ := trace_index_steps next (alloc.vec.Vec.len rows) index hn
      (by simpa only [alloc.vec.Vec.len,Slice.len_val,Slice.length] using hl)
      (by simpa only [alloc.vec.Vec.len,Slice.len_val,Slice.length] using hi)
    obtain ⟨wide,hw⟩ := CuSavingsRhoDiagnostics.from_qm31_total (rows.val[index.val]'hi)
    obtain ⟨wide1,hw1⟩ := CuSavingsRhoDiagnostics.from_m31_total b
    change from_m31 (basis.val[index.val]'hb) = .ok wide1 at hw1
    simp only [hprod,hadd,bind_tc_ok,vec_read rows index hi,
      AspisR1RhoCoefficients.aspis_core.field.WideExact.from_qm31,hw,
      AspisR1RhoCoefficients.aspis_core.field.WideExact.from_m31,hw1,
      AspisR1RhoCoefficients.trace.value,trace.value]
    rfl

#print axioms source_body
end AspisR1.CuSavingsRhoOptimizedTraversal
