import CuSavingsRhoUpdateLoop
import CuSavingsRhoFlushArray

/-! Exact source push contract: the emitted update, actual low-bit flush
predicate, mutable array iteration and Vec handback compose to rhoStep on every
limb. The Vec frame and unchanged term counter are explicit in replaceRow.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoPush
open Aeneas Aeneas.Std Result
open AspisR1CuRho
open AspisR1.CuSavingsRhoValue
open AspisR1.CuSavingsRhoPushStep
open AspisR1.CuSavingsRhoState
open AspisR1.CuSavingsRhoFlushArray
open AspisR1.CuSavingsResidues
open AspisV8R17.RawReducer

def powerLimbs (power : field.QM31) : Limbs :=
  Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]

def flushRow (self : verifier.BatchedWeights) (index : Usize) : Result verifier.BatchedWeights := do
  let (row,indexBack) ← alloc.vec.Vec.index_mut
    (Aeneas.Std.core.slice.index.SliceIndexUsizeSlice Raw4) self.raw index
  let (iter,intoBack) ←
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter row
  let (last,back) ← verifier.BatchedWeights.push_loop1 iter (fun out => out)
  .ok {self with «raw» := indexBack (intoBack (back last))}

theorem flushRow_success (self : verifier.BatchedWeights) (index : Usize)
    (hi : index.val < self.raw.val.length) :
    flushRow self index =
      .ok (replaceRow self index (foldedArray (self.raw.val[index.val]'hi))) := by
  let row := self.raw.val[index.val]'hi
  obtain ⟨last,back,hrun,hfold⟩ := AspisR1.CuSavingsRhoFlushArray.source_success row
  simp only [flushRow,vec_read_mut self.raw index hi,bind_tc_ok,
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter]
  change (do
    let pair ← verifier.BatchedWeights.push_loop1 (initialIter row) (fun out => out)
    Result.ok (replaceRow self index (Array.from_slice row (pair.2 pair.1).slice))) = _
  rw [hrun]
  change Result.ok (replaceRow self index (Array.from_slice row (back last).slice)) = _
  rw [hfold]

theorem push_eq (self : verifier.BatchedWeights) (index : Usize)
    (power : field.QM31) (basis : field.M31) :
    verifier.BatchedWeights.push self index power basis = (do
      let updated ← verifier.BatchedWeights.push_loop0 {start:=0#usize,«end»:=4#usize}
        self index basis (powerLimbs power)
      if UScalar.and updated.terms 3#usize = 3#usize then flushRow updated index
      else .ok updated) := by
  simp only [verifier.BatchedWeights.push,powerLimbs,flushRow,lift,bind_tc_ok]
  rfl

theorem flush_iff (self : verifier.BatchedWeights) :
    UScalar.and self.terms 3#usize = 3#usize ↔ self.terms.val%4=3 := by
  constructor
  · intro h
    have hv := congrArg UScalar.val h
    rw [AspisR1.CuSavingsRhoScalar.source_flush_condition] at hv
    simpa using hv
  · intro h
    apply UScalar.eq_of_val_eq
    rw [AspisR1.CuSavingsRhoScalar.source_flush_condition]
    simpa using h

theorem source_values (self : verifier.BatchedWeights) (index : Usize)
    (power : field.QM31) (basis : field.M31) (hi : index.val < self.raw.val.length)
    (hr : ∀ j : Fin 4, RhoBound (wordAt (self.raw.val[index.val]'hi) j).val self.terms.val)
    (hp : ∀ j : Fin 4, (wordAt (powerLimbs power) j).val < P) (hb : basis.val < P) :
    ∃ row : Raw4,
      verifier.BatchedWeights.push self index power basis = .ok (replaceRow self index row) ∧
      ∀ j : Fin 4, (wordAt row j).val =
        rhoStep (wordAt (self.raw.val[index.val]'hi) j).val self.terms.val
          ((wordAt (powerLimbs power) j).val*basis.val) := by
  obtain ⟨row1,hupdate,hvalues⟩ := AspisR1.CuSavingsRhoUpdateLoop.source_success
    self index basis (powerLimbs power) hi hr hp hb
  let updated := replaceRow self index row1
  have hi1 : index.val < updated.raw.val.length := by rw [replace_length];exact hi
  have hrow1 : updated.raw.val[index.val]'hi1 = row1 := replace_read self index row1 hi
  by_cases hc : self.terms.val%4=3
  · have hcond : UScalar.and updated.terms 3#usize = 3#usize :=
      (flush_iff updated).mpr hc
    have hflush := flushRow_success updated index hi1
    rw [hrow1] at hflush
    refine ⟨foldedArray row1,?_,?_⟩
    · rw [push_eq,hupdate]
      change (if UScalar.and updated.terms 3#usize = 3#usize then
        flushRow updated index else .ok updated) = _
      rw [if_pos hcond,hflush,replace_twice]
    · intro j
      rw [word_folded_val,hvalues j]
      simp only [rhoStep,if_pos hc]
  · have hcond : ¬ UScalar.and updated.terms 3#usize = 3#usize :=
      fun h => hc ((flush_iff updated).mp h)
    refine ⟨row1,?_,?_⟩
    · rw [push_eq,hupdate]
      change (if UScalar.and updated.terms 3#usize = 3#usize then
        flushRow updated index else .ok updated) = _
      rw [if_neg hcond]
    · intro j
      rw [hvalues j]
      simp only [rhoStep,if_neg hc]

theorem source_success (self : verifier.BatchedWeights) (index : Usize)
    (power : field.QM31) (basis : field.M31) (hi : index.val < self.raw.val.length)
    (hr : ∀ j : Fin 4, RhoBound (wordAt (self.raw.val[index.val]'hi) j).val self.terms.val)
    (hp : ∀ j : Fin 4, (wordAt (powerLimbs power) j).val < P) (hb : basis.val < P) :
    ∃ row : Raw4,
      verifier.BatchedWeights.push self index power basis = .ok (replaceRow self index row) ∧
      ∀ j : Fin 4,
        RhoBound (wordAt row j).val (self.terms.val+1) ∧
        (wordAt row j).val%P =
          ((wordAt (self.raw.val[index.val]'hi) j).val +
            (wordAt (powerLimbs power) j).val*basis.val)%P := by
  obtain ⟨row,hrun,hvalues⟩ := source_values self index power basis hi hr hp hb
  refine ⟨row,hrun,?_⟩
  intro j
  rw [hvalues j]
  exact ⟨rhoStep_bound _ _ _ (hr j) (canonical_product_bound _ _ (hp j) hb),rhoStep_mod _ _ _⟩

#print axioms flushRow_success
#print axioms push_eq
#print axioms flush_iff
#print axioms source_values
#print axioms source_success
end AspisR1.CuSavingsRhoPush
