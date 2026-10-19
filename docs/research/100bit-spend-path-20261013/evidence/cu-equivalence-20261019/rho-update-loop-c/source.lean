import CuSavingsRhoState
import OccupancyRangeTraversal

/-! Full induction over the actual four-coordinate update loop. The output is
an exact replacement of the selected Vec row; every other row and the term
counter are preserved. Each selected coordinate receives exactly one product.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoUpdateLoop
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1CuRho
open AspisR1.CuSavingsRhoValue
open AspisR1.CuSavingsRhoPushStep
open AspisR1.CuSavingsRhoState
open AspisR1.CuSavingsResidues
open AspisV8R17.RawReducer

theorem loop_unroll (iter : Range) (self : verifier.BatchedWeights) (index : Usize)
    (basis : field.M31) (limbs : Limbs) :
    verifier.BatchedWeights.push_loop0 iter self index basis limbs = (do
      let result ← verifier.BatchedWeights.push_loop0.body index limbs iter self basis
      match result with
      | .done out => .ok out
      | .cont (next,state,scalar) =>
        verifier.BatchedWeights.push_loop0 next state index scalar limbs) := by
  unfold verifier.BatchedWeights.push_loop0
  rw [loop]
  simp only [Prod.casesOn]
  cases h : verifier.BatchedWeights.push_loop0.body index limbs iter self basis with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok result => cases result <;> simp only [h,bind_tc_ok] <;> rfl

theorem loop_success_fuel (fuel : Nat) (self : verifier.BatchedWeights)
    (index : Usize) (basis : field.M31) (limbs : Limbs) (iter : Range)
    (hi : index.val < self.raw.val.length) (hend : iter.end.val ≤ 4)
    (hspan : iter.start.val+fuel=iter.end.val)
    (hr : ∀ j : Fin 4, iter.start.val ≤ j.val →
      RhoBound (wordAt (self.raw.val[index.val]'hi) j).val self.terms.val)
    (hp : ∀ j : Fin 4, (wordAt limbs j).val < P) (hb : basis.val < P) :
    ∃ row : Raw4,
      verifier.BatchedWeights.push_loop0 iter self index basis limbs =
        .ok (replaceRow self index row) ∧
      ∀ j : Fin 4, (wordAt row j).val =
        if iter.start.val ≤ j.val ∧ j.val < iter.end.val then
          (wordAt (self.raw.val[index.val]'hi) j).val + (wordAt limbs j).val*basis.val
        else (wordAt (self.raw.val[index.val]'hi) j).val := by
  induction fuel generalizing self iter with
  | zero =>
    let row := self.raw.val[index.val]'hi
    have hstop : iter.start.val ≥ iter.end.val := by omega
    have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
    refine ⟨row,?_,?_⟩
    · rw [loop_unroll]
      have hbody : verifier.BatchedWeights.push_loop0.body index limbs iter self basis =
          .ok (.done self) := by
        simp only [verifier.BatchedWeights.push_loop0.body,hnext,bind_tc_ok]
        rfl
      rw [hbody]
      change Result.ok self = Result.ok (replaceRow self index (self.raw.val[index.val]'hi))
      rw [replace_self]
    · intro j
      rw [if_neg (by omega)]
  | succ fuel ih =>
    have hactive : iter.start.val < iter.end.val := by omega
    have hidx : iter.start.val < 4 := by omega
    obtain ⟨next,hnext,hinc,hend1,_⟩ :=
      AspisR1.OccupancyRangeTraversal.next_step iter hactive
    obtain ⟨value,hbody,hvalue⟩ := source_update_step self index basis limbs iter next
      iter.start hnext hi hidx (hr ⟨iter.start.val,hidx⟩ (Nat.le_refl _))
      (hp ⟨iter.start.val,hidx⟩) hb
    let old := self.raw.val[index.val]'hi
    let row1 := old.set iter.start value
    let state1 := replaceRow self index row1
    have hi1 : index.val < state1.raw.val.length := by
      rw [replace_length];exact hi
    have hrow1 : state1.raw.val[index.val]'hi1 = row1 := replace_read self index row1 hi
    have hr1 : ∀ j : Fin 4, next.start.val ≤ j.val →
        RhoBound (wordAt (state1.raw.val[index.val]'hi1) j).val state1.terms.val := by
      intro j hj
      rw [hrow1,replace_terms]
      change RhoBound (wordAt (old.set iter.start value) j).val self.terms.val
      rw [word_set,if_neg (by rw [hinc] at hj;omega)]
      exact hr j (by rw [hinc] at hj;omega)
    obtain ⟨row,hrun,hmodel⟩ := ih state1 next hi1
      (by rw [hend1];exact hend) (by rw [hend1];omega) hr1
    refine ⟨row,?_,?_⟩
    · rw [loop_unroll,hbody]
      change verifier.BatchedWeights.push_loop0 next state1 index basis limbs = _
      rw [hrun,replace_twice]
    · intro j
      have hj := hmodel j
      rw [hrow1,hinc,hend1] at hj
      by_cases heq : j.val = iter.start.val
      · have hafter : ¬(iter.start.val+1 ≤ j.val ∧ j.val < iter.end.val) := by omega
        have hinside : iter.start.val ≤ j.val ∧ j.val < iter.end.val := by omega
        rw [if_neg hafter] at hj
        rw [hj,if_pos hinside]
        change (wordAt (old.set iter.start value) j).val = _
        rw [word_set,if_pos heq]
        have hj0 : (⟨iter.start.val,hidx⟩ : Fin 4) = j := Fin.ext heq.symm
        simpa only [hj0] using hvalue
      · have hcell : wordAt row1 j = wordAt old j := by
          change wordAt (old.set iter.start value) j = _
          rw [word_set,if_neg heq]
        rw [hcell] at hj
        have hrange : (iter.start.val+1 ≤ j.val ∧ j.val < iter.end.val) ↔
            (iter.start.val ≤ j.val ∧ j.val < iter.end.val) := by omega
        simpa only [hrange] using hj

theorem source_success (self : verifier.BatchedWeights) (index : Usize)
    (basis : field.M31) (limbs : Limbs) (hi : index.val < self.raw.val.length)
    (hr : ∀ j : Fin 4, RhoBound (wordAt (self.raw.val[index.val]'hi) j).val self.terms.val)
    (hp : ∀ j : Fin 4, (wordAt limbs j).val < P) (hb : basis.val < P) :
    ∃ row : Raw4,
      verifier.BatchedWeights.push_loop0 {start:=0#usize,«end»:=4#usize}
        self index basis limbs = .ok (replaceRow self index row) ∧
      ∀ j : Fin 4, (wordAt row j).val =
        (wordAt (self.raw.val[index.val]'hi) j).val + (wordAt limbs j).val*basis.val := by
  obtain ⟨row,hrun,hmodel⟩ := loop_success_fuel 4 self index basis limbs
    {start:=0#usize,«end»:=4#usize} hi (by decide) (by decide) (fun j _ => hr j) hp hb
  refine ⟨row,hrun,?_⟩
  intro j
  have hj := hmodel j
  have hinside : (0#usize).val ≤ j.val ∧ j.val < (4#usize).val := by
    simpa using (And.intro (Nat.zero_le j.val) j.isLt)
  simpa only [if_pos hinside] using hj

#print axioms loop_unroll
#print axioms loop_success_fuel
#print axioms source_success
end AspisR1.CuSavingsRhoUpdateLoop
