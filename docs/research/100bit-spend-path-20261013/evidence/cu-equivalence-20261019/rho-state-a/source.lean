import CuSavingsRhoPushStep

/-! Frame identities for the Vec/array updates in the actual rho loop.
No arithmetic or iterator behavior is assumed by these structural lemmas. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoState
open Aeneas Aeneas.Std Result
open AspisR1CuRho
open AspisR1.CuSavingsRhoPushStep
open AspisR1.CuSavingsRhoValue

def replaceRow (self : verifier.BatchedWeights) (index : Usize) (row : Raw4) :
    verifier.BatchedWeights :=
  {self with «raw» := Slice.set self.raw index row}

theorem replace_length (self : verifier.BatchedWeights) (index : Usize) (row : Raw4) :
    (replaceRow self index row).raw.val.length = self.raw.val.length := by
  simp only [replaceRow,Slice.set,Slice.setAtNat,List.length_set]

theorem replace_terms (self : verifier.BatchedWeights) (index : Usize) (row : Raw4) :
    (replaceRow self index row).terms = self.terms := rfl

theorem replace_read (self : verifier.BatchedWeights) (index : Usize) (row : Raw4)
    (hi : index.val < self.raw.val.length) :
    (replaceRow self index row).raw.val[index.val]'
      (by rw [replace_length];exact hi) = row := by
  simp only [replaceRow,Slice.set,Slice.setAtNat]
  exact List.getElem_set_self (by simpa only [List.length_set] using hi)

theorem replace_self (self : verifier.BatchedWeights) (index : Usize)
    (hi : index.val < self.raw.val.length) :
    replaceRow self index (self.raw.val[index.val]'hi) = self := by
  cases self with
  | mk values count =>
    unfold replaceRow
    congr 1
    apply Subtype.ext
    simp only [Slice.set,Slice.setAtNat]
    exact List.set_getElem_self

theorem replace_twice (self : verifier.BatchedWeights) (index : Usize) (a b : Raw4) :
    replaceRow (replaceRow self index a) index b = replaceRow self index b := by
  cases self with
  | mk values count =>
    unfold replaceRow
    congr 1
    apply Subtype.ext
    simp only [Slice.set,Slice.setAtNat,List.set_set]

theorem word_set (a : Raw4) (index : Usize) (value : U64) (j : Fin 4) :
    wordAt (a.set index value) j =
      if j.val = index.val then value else wordAt a j := by
  unfold wordAt
  simp only [Array.set]
  rw [List.getElem_set]
  split
  · rename_i h
    rw [if_pos h.symm]
  · rename_i h
    rw [if_neg (Ne.symm h)]

#print axioms replace_length
#print axioms replace_read
#print axioms replace_self
#print axioms replace_twice
#print axioms word_set
end AspisR1.CuSavingsRhoState
