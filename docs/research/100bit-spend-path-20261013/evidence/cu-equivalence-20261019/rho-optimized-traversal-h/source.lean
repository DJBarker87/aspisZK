import AspisR1RhoOptimizedLoop.Funs
import CuSavingsRhoSourceOption
import CuSavingsRhoReferenceTraversal
import CuSavingsRhoQueryBatch

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


theorem loop_unroll (iter : Range) (back : Option BW → Option BW)
    (rows : Rows) (power : field.QM31) (next : Usize) (basis : Basis)
    (pending : Option BW) :
    sourceLoop iter back rows power next basis pending = (do
      let result ← Source power next basis iter back rows pending
      match result with
      | .done out => .ok out
      | .cont (iter1,back1,rows1,pending1) =>
        sourceLoop iter1 back1 rows1 power next basis pending1) := by
  unfold sourceLoop AspisR1RhoCoefficients.rho_new.coefficients_loop
  rw [loop]
  simp only [Prod.casesOn]
  cases hb : Source power next basis iter back rows pending with
  | fail error => simp only [hb,bind_tc_fail]
  | div => simp only [hb,bind_tc_div]
  | ok control => cases control <;> simp only [hb,bind_tc_ok] <;> rfl

def pairs (basis : Basis) (is : List Usize) : List (Usize × U32) :=
  is.map (fun i => (i,basisWord basis i))

theorem source_traverse (fuel : Nat) (iter : Range) (back : Option BW → Option BW)
    (rows : Rows) (self : BW) (power : field.QM31) (next : Usize) (basis : Basis)
    (hn : next.val ≤ 22) (hl : rows.val.length ≤ 256)
    (hsize : rows.val.length=iter.«end».val)
    (hspan : iter.start.val+fuel=iter.«end».val) :
    sourceLoop iter back rows power next basis (some self) = (do
      let out ← updates power (pairs basis (indices iter.start.val fuel)) self
      .ok (rows,some out,back)) := by
  induction fuel generalizing iter self with
  | zero =>
    have hd := OccupancyRangeTraversal.next_done iter (by omega)
    rw [loop_unroll]
    simp only [Source,AspisR1RhoCoefficients.rho_new.coefficients_loop.body,hd,
      bind_tc_ok,uncurry_apply_pair,indices,List.range'_zero,List.map_nil,pairs,updates]
  | succ fuel ih =>
    obtain ⟨iter1,hiter,hstart,hend,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    have hi : iter.start.val < rows.val.length := by omega
    have hb : iter.start.val < basis.val.length := by
      have h : iter.start.val < 256 := Nat.lt_of_lt_of_le hi hl
      simpa only [basis.property,show (256#usize).val=256 by scalar_tac] using h
    have hbody := source_body power next basis iter iter1 iter.start rows self back hn hl hi hiter
    rw [loop_unroll,hbody]
    simp only [indices,List.range'_succ,List.map_cons,word_scalar,pairs,
      basisWord,List.getElem?_eq_getElem hb,Option.getD_some,updates]
    cases hs : verifier.BatchedWeights.push self iter.start power (basis.val[iter.start.val]'hb) with
    | fail error => simp only [hs,bind_tc_fail]
    | div => simp only [hs,bind_tc_div]
    | ok out =>
      simp only [hs,bind_tc_ok]
      have hsize' : rows.val.length=iter1.«end».val := by rw [hend];exact hsize
      have hspan' : iter1.start.val+fuel=iter1.«end».val := by rw [hstart,hend];omega
      simpa only [hstart,pairs,indices,basisWord] using ih iter1 out hsize' hspan'

theorem source_eq_some (rows : Rows) (self : BW) (power : field.QM31)
    (next : Usize) (basis : Basis)
    (hn : next.val ≤ 22) (hl : (alloc.vec.Vec.len rows).val ≤ 256) :
    AspisR1RhoCoefficients.rho_new.coefficients rows power next basis (some self) = (do
      let out ← CuSavingsRhoQueryBatch.batch power
        (CuSavingsRhoInputs.items basis (alloc.vec.Vec.len rows) hl) self
      .ok (rows,some out)) := by
  unfold AspisR1RhoCoefficients.rho_new.coefficients
  dsimp only
  have hlen : (alloc.vec.Vec.len rows).val=rows.val.length := by
    simp only [alloc.vec.Vec.len,Slice.len_val,Slice.length]
  have heq := source_traverse (alloc.vec.Vec.len rows).val
    {start:=0#usize,«end»:=alloc.vec.Vec.len rows} (fun o => o) rows self power next basis hn
    (by rw [← hlen];exact hl) hlen.symm (by simp only [show (0#usize).val=0 by scalar_tac,Nat.zero_add])
  unfold sourceLoop at heq
  rw [heq]
  simp only [show (0#usize).val=0 by scalar_tac,pairs,pairs_eq basis (alloc.vec.Vec.len rows) hl]
  change (do
    let (rows1,pending1,back) ← (do
      let out ← updates power (CuSavingsRhoInputs.items basis (alloc.vec.Vec.len rows) hl) self
      .ok (rows,some out,fun o => o))
    match pending1 with
    | none => .ok (rows1,back none)
    | some weights => do
      let terms ← weights.terms+1#usize
      .ok (rows1,back (some {weights with terms:=terms}))) = _
  unfold CuSavingsRhoQueryBatch.batch
  cases hu : updates power (CuSavingsRhoInputs.items basis (alloc.vec.Vec.len rows) hl) self with
  | fail error => rfl
  | div => rfl
  | ok out =>
    simp only [bind_tc_ok,uncurry_apply_pair]
    change (do
      let terms ← UScalar.add out.terms 1#usize
      .ok (rows,some {out with terms:=terms})) =
      (do
        let updated ← (do
          let terms ← UScalar.add out.terms 1#usize
          .ok {out with terms:=terms})
        .ok (rows,some updated))
    cases ht : UScalar.add out.terms 1#usize <;> rfl

#print axioms source_traverse
#print axioms source_eq_some

#print axioms source_body
end AspisR1.CuSavingsRhoOptimizedTraversal
