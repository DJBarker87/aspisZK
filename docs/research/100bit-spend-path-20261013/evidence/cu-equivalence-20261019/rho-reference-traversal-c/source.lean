import CuSavingsRhoReferenceLoop
import CuSavingsRhoRangeInputs

/-! Consume the entire actual emitted reference loop, not an assumed input
list. No canonicality/success premise is needed for this source traversal. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoReferenceTraversal
open Aeneas Aeneas.Std Result ControlFlow AspisR1CuRho
open CuSavingsRhoReference CuSavingsRhoVector CuSavingsRhoReferenceLoop
open CuSavingsRangeTraversal CuSavingsRhoRangeInputs
abbrev Rows := alloc.vec.Vec AspisR1RhoCoefficients.aspis_core.field.QM31
abbrev Range := core.ops.range.Range Usize
abbrev Basis := Array U32 256#usize
abbrev sourceLoop := AspisR1RhoCoefficients.rho_old.coefficients_loop

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem reference_length (rows out : Rows) (index : Usize) (power : field.QM31)
    (basis : U32) (h : referenceAt rows index power basis = .ok out) :
    out.val.length = rows.val.length := by
  unfold referenceAt at h
  obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
  obtain ⟨value,_,h⟩ := bind_ok _ _ _ h
  cases Result.ok.inj h
  exact Slice.set_length rows index value

def atBasis (power : field.QM31) (basis : Basis) (index : Usize) (rows : Rows) :
    Result Rows := referenceAt rows index power (basisWord basis index)

theorem loop_unroll (iter : Range) (rows : Rows) (power : field.QM31)
    (next : Usize) (basis : Basis) : sourceLoop iter rows power next basis = (do
      let result ← Source power next basis iter rows
      match result with
      | .done out => .ok out
      | .cont (iter1,rows1) => sourceLoop iter1 rows1 power next basis) := by
  unfold sourceLoop AspisR1RhoCoefficients.rho_old.coefficients_loop
  rw [loop]
  simp only [Prod.casesOn]
  cases hb : Source power next basis iter rows with
  | fail error => simp only [hb,bind_tc_fail]
  | div => simp only [hb,bind_tc_div]
  | ok control => cases control <;> simp only [hb,bind_tc_ok] <;> rfl

theorem source_traverse (fuel : Nat) (iter : Range) (rows : Rows)
    (power : field.QM31) (next : Usize) (basis : Basis)
    (hn : next.val ≤ 22) (hl : rows.val.length ≤ 256)
    (hsize : rows.val.length=iter.«end».val)
    (hspan : iter.start.val+fuel=iter.«end».val) :
    sourceLoop iter rows power next basis =
      CuSavingsRangeTraversal.traverse (atBasis power basis) (indices iter.start.val fuel) rows := by
  induction fuel generalizing iter rows with
  | zero =>
    have hd := OccupancyRangeTraversal.next_done iter (by omega)
    rw [loop_unroll]
    simp only [Source,AspisR1RhoCoefficients.rho_old.coefficients_loop.body,hd,
      bind_tc_ok,uncurry_apply_pair,indices,List.range'_zero,List.map_nil,CuSavingsRangeTraversal.traverse]
  | succ fuel ih =>
    obtain ⟨iter1,hiter,hstart,hend,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    have hi : iter.start.val < rows.val.length := by omega
    have hb : iter.start.val < basis.val.length := by
      have h : iter.start.val < 256 := Nat.lt_of_lt_of_le hi hl
      simpa only [basis.property,show (256#usize).val=256 by scalar_tac] using h
    have hbody := source_body power next basis iter iter1 iter.start rows hn hl hi hiter
    rw [loop_unroll,hbody]
    simp only [indices,List.range'_succ,List.map_cons,word_scalar,CuSavingsRangeTraversal.traverse,atBasis,
      basisWord,List.getElem?_eq_getElem hb,Option.getD_some]
    cases hs : referenceAt rows iter.start power (basis.val[iter.start.val]'hb) with
    | fail error => simp only [hs,bind_tc_fail];rfl
    | div => simp only [hs,bind_tc_div];rfl
    | ok out =>
      simp only [hs,bind_tc_ok]
      change sourceLoop iter1 out power next basis =
        CuSavingsRangeTraversal.traverse (atBasis power basis)
          (List.map word (List.range' (iter.start.val+1) fuel)) out
      have hlength := reference_length rows out iter.start power _ hs
      have hsize' : out.val.length=iter1.«end».val := by rw [hlength,hsize,hend]
      have hspan' : iter1.start.val+fuel=iter1.«end».val := by rw [hstart,hend];omega
      simpa only [hstart,indices] using ih iter1 out (by rw [hlength];exact hl) hsize' hspan'

theorem traverse_pairs (power : field.QM31) (basis : Basis) (is : List Usize) (rows : Rows) :
    CuSavingsRangeTraversal.traverse (atBasis power basis) is rows =
      referenceUpdates power (is.map (fun i => (i,basisWord basis i))) rows := by
  induction is generalizing rows with
  | nil => rfl
  | cons i tail ih =>
    simp only [CuSavingsRangeTraversal.traverse,List.map_cons,referenceUpdates,atBasis]
    cases h : referenceAt rows i power (basisWord basis i) with
    | fail error => rfl
    | div => rfl
    | ok out =>
      change CuSavingsRangeTraversal.traverse (atBasis power basis) tail out =
        referenceUpdates power (tail.map (fun i => (i,basisWord basis i))) out
      exact ih out

theorem source_eq (rows : Rows) (power : field.QM31) (next : Usize) (basis : Basis)
    (hn : next.val ≤ 22) (hl : (alloc.vec.Vec.len rows).val ≤ 256) :
    AspisR1RhoCoefficients.rho_old.coefficients rows power next basis =
      referenceUpdates power
        (CuSavingsRhoInputs.items basis (alloc.vec.Vec.len rows) hl) rows := by
  unfold AspisR1RhoCoefficients.rho_old.coefficients
  change sourceLoop {start:=0#usize,«end»:=alloc.vec.Vec.len rows} rows power next basis = _
  have hlen : (alloc.vec.Vec.len rows).val=rows.val.length := by
    simp only [alloc.vec.Vec.len,Slice.len_val,Slice.length]
  rw [source_traverse (alloc.vec.Vec.len rows).val
    {start:=0#usize,«end»:=alloc.vec.Vec.len rows} rows power next basis hn
    (by rw [← hlen];exact hl) hlen.symm
    (by simp only [show (0#usize).val=0 by scalar_tac,Nat.zero_add])]
  rw [traverse_pairs]
  exact congrArg (fun is => referenceUpdates power is rows) (pairs_eq basis _ hl)

#print axioms reference_length
#print axioms source_traverse
#print axioms source_eq
end AspisR1.CuSavingsRhoReferenceTraversal
