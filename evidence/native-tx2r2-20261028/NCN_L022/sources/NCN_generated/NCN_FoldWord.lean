import NCI_ResidueWords
import NCI_ResidueInvariant
set_option autoImplicit false
namespace AspisR1.NCN_FoldWord
open Aeneas Aeneas.Std Result

def source (x : U64) : Result U64 := do
  let lo ← lift (x &&& 2147483647#u64)
  let hi ← x >>> 31#i32
  lo + hi

/-- Exact selected checked word operations for one flush cell; no word-result
or no-overflow observation is assumed as an input. -/
theorem source_ok (x : U64) :
    ∃ out : U64, source x=ok out ∧ out.val=NCI_ResidueInvariant.fold x.val ∧
      out.val<NCI_ResidueBounds.Boundary := by
  have hx : x.val<18446744073709551616 := by scalar_tac
  have low : (x &&& 2147483647#u64).val=x.val%2147483648 := by
    change x.val &&& 2147483647 = x.val%2147483648
    simpa using Nat.and_two_pow_sub_one_eq_mod x.val 31
  have hiBound : x.val/2147483648<18446744073709551616 := by
    have h := Nat.div_le_self x.val 2147483648
    omega
  obtain ⟨hi,_,hiVal⟩ := NCI_ResidueWords.word_exists (x.val/2147483648) hiBound
  have shiftVal : (UScalar.mk (x.bv.ushiftRight 31) : U64).val=x.val/2147483648 := by
    change x.val >>> (31 : Nat)=x.val/2147483648
    rw [Nat.shiftRight_eq_div_pow]
    rfl
  have same : (UScalar.mk (x.bv.ushiftRight 31) : U64)=hi := by scalar_tac
  have shift : x >>> 31#i32=ok hi := by
    change UScalar.shiftRight x 31=ok hi
    simp only [UScalar.shiftRight]
    rw [if_pos (show 31<(UScalarTy.U64).numBits by decide)]
    exact congrArg Result.ok same
  have small := NCI_ResidueBounds.fold_boundary x.val hx
  have fit : NCI_ResidueInvariant.fold x.val<18446744073709551616 := by
    unfold NCI_ResidueInvariant.fold
    unfold NCI_ResidueBounds.Boundary at small
    omega
  obtain ⟨out,mk,outVal⟩ := NCI_ResidueWords.word_exists (NCI_ResidueInvariant.fold x.val) fit
  refine ⟨out,?_,outVal,?_⟩
  · simp only [source,bind_tc_ok,shift]
    change UScalar.tryMk .U64 ((x &&& 2147483647#u64).val+hi.val)=ok out
    rw [low,hiVal]
    exact mk
  · rw [outVal]
    exact small

#print axioms source_ok
end AspisR1.NCN_FoldWord
