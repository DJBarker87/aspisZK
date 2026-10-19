import AspisR1RhoReferenceLoop.Funs
import CuSavingsRhoDiagnostics
import CuSavingsRangeTraversal
import CuSavingsRhoInputs

/-! Bind the entire emitted reference coefficient loop to the arithmetic
pipeline. Diagnostic conversions execute and checked diagnostic indices fit.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoReferenceLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1CuRho
open CuSavingsRhoReference CuSavingsRhoVector CuSavingsRhoPushStep
abbrev Source := AspisR1RhoCoefficients.rho_old.coefficients_loop.body
abbrev Range := core.ops.range.Range Usize
abbrev Basis := Array U32 256#usize

def traceIndex (next length index : Usize) : Result Usize := do
  let product ← next * length
  product + index

theorem trace_index_steps (next length index : Usize) (hn : next.val ≤ 22)
    (hl : length.val ≤ 256) (hi : index.val < length.val) :
    ∃ product out,(next*length : Result Usize) = .ok product ∧
      (product+index : Result Usize) = .ok out := by
  have hb : next.val*length.val ≤ 22*256 := Nat.mul_le_mul hn hl
  have hlarge : 6000 < 2^UScalarTy.Usize.numBits := by scalar_tac
  obtain ⟨product,hm,hv⟩ := ExtractedCurrentReducerOps.tryMk_success (ty:=.Usize)
    (next.val*length.val) (by omega)
  change (next*length : Result Usize) = .ok product at hm
  obtain ⟨out,ha,_⟩ := ExtractedCurrentReducerOps.tryMk_success (ty:=.Usize)
    (product.val+index.val) (by rw [hv];omega)
  change (product+index : Result Usize) = .ok out at ha
  exact ⟨product,out,hm,ha⟩

theorem array_read (basis : Basis) (index : Usize) (hi : index.val < basis.val.length) :
    Array.index_usize basis index = .ok (basis.val[index.val]'hi) := by
  simp only [Array.index_usize,Array.getElem?_Usize_eq,List.getElem?_eq_getElem hi]

theorem arithmetic_eq (weight power : field.QM31) (basis : U32) :
    (do let product ← AspisR1RhoCoefficients.QM31.mul_m31 power basis
        AspisR1RhoCoefficients.aspis_core.field.QM31.add weight product) =
      referenceStep weight power basis := by
  unfold AspisR1RhoCoefficients.QM31.mul_m31
    AspisR1RhoCoefficients.aspis_core.field.QM31.add referenceStep AspisR1RhoReference.step
  cases hm : AspisR1RhoReference.field.QM31.mul_m31 (toCurrent power) basis with
  | fail error => rfl
  | div => rfl
  | ok product =>
    simp only [bind_tc_ok]
    rfl

theorem source_body (power : field.QM31) (next : Usize) (basis : Basis)
    (iter after : Range) (index : Usize) (rows : alloc.vec.Vec AspisR1RhoCoefficients.aspis_core.field.QM31)
    (hn : next.val ≤ 22) (hl : rows.val.length ≤ 256)
    (hi : index.val < rows.val.length)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some index,after)) :
    Source power next basis iter rows = (do
      let out ← referenceAt rows index power (basis.val[index.val]'(by
        have hi' : index.val < 256 := Nat.lt_of_lt_of_le hi hl
        simpa only [basis.property,show (256#usize).val=256 by scalar_tac] using hi'))
      .ok (.cont (after,out))) := by
  have hb : index.val < basis.val.length := by
    have hi' : index.val < 256 := Nat.lt_of_lt_of_le hi hl
    simpa only [basis.property,show (256#usize).val=256 by scalar_tac] using hi'
  let b := basis.val[index.val]'hb
  rw [Source,AspisR1RhoCoefficients.rho_old.coefficients_loop.body,hnext]
  dsimp only
  simp only [bind_tc_ok,uncurry_apply_pair,vec_read rows index hi,array_read basis index hb]
  unfold referenceAt
  rw [vec_read rows index hi]
  simp only [bind_tc_ok]
  rw [← arithmetic_eq]
  cases hm : AspisR1RhoCoefficients.QM31.mul_m31 power b with
  | fail error => simp only [hm,bind_tc_fail]
  | div => simp only [hm,bind_tc_div]
  | ok product =>
    simp only [hm,bind_tc_ok]
    cases ha : AspisR1RhoCoefficients.aspis_core.field.QM31.add (rows.val[index.val]'hi) product with
    | fail error => simp only [ha,bind_tc_fail]
    | div => simp only [ha,bind_tc_div]
    | ok value =>
      simp only [ha,bind_tc_ok,vec_read_mut rows index hi]
      change (do
        let i1 ← next * alloc.vec.Vec.len (Slice.set rows index value)
        let i2 ← i1 + index
        let q3 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice field.QM31)
          (Slice.set rows index value) index
        let we ← field.WideExact.from_qm31 q3
        trace.value 12#u16 i2 we
        let i4 ← next * alloc.vec.Vec.len (Slice.set rows index value)
        let i5 ← i4 + index
        let we1 ← from_m31 b
        trace.value 13#u16 i5 we1
        .ok (.cont (after,Slice.set rows index value) : ControlFlow (Range × Slice field.QM31) (Slice field.QM31))) = _
      have hlen : alloc.vec.Vec.len (Slice.set rows index value) = alloc.vec.Vec.len rows := by
        apply UScalar.eq_of_val_eq
        simp only [alloc.vec.Vec.len,Slice.len_val,Slice.length,Slice.set_length]
      rw [hlen]
      obtain ⟨productIndex,ix,hprod,hadd⟩ := trace_index_steps next (alloc.vec.Vec.len rows) index hn
        (by simpa only [alloc.vec.Vec.len,Slice.len_val,Slice.length] using hl)
        (by simpa only [alloc.vec.Vec.len,Slice.len_val,Slice.length] using hi)
      obtain ⟨wide,hw⟩ := CuSavingsRhoDiagnostics.from_qm31_total value
      obtain ⟨wide1,hw1⟩ := CuSavingsRhoDiagnostics.from_m31_total b
      have hread : (Slice.set rows index value).val[index.val]'(by
          simpa only [Slice.set_length] using hi) = value := by
        simp only [Slice.set,Slice.setAtNat,List.getElem_set_self]
      simp only [hprod,hadd,bind_tc_ok,vec_read (Slice.set rows index value) index
        (by simpa only [Slice.set_length] using hi),hread,
        AspisR1RhoCoefficients.aspis_core.field.WideExact.from_qm31,hw,
        AspisR1RhoCoefficients.aspis_core.field.WideExact.from_m31,hw1,
        AspisR1RhoCoefficients.trace.value,trace.value]

#print axioms trace_index_steps
#print axioms arithmetic_eq
#print axioms source_body
end AspisR1.CuSavingsRhoReferenceLoop
