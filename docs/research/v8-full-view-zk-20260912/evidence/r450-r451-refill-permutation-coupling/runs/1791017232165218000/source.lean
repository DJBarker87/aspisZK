import AspisV8R19.R451BlockStoppingCore
import AspisV8R19.R449BlockPermutation

set_option autoImplicit false
namespace AspisV8R19.R451BlockStoppingPermutation
open AspisV8R19.R444InitialSourceLimb
open AspisV8R19.R421UniformMasked31Block
open AspisV8R19.R442RejectionAlphabet
open AspisV8R19.R445InitialBlockRejectionLaw
open AspisV8R19.R449BlockPermutation

theorem scanAt_count_blockPerm (σ : Equiv.Perm (Fin modulus))
    (block : AspisV8R19.SourceDuplexStep.State) :
    (scanAt (blockPerm σ block) 0 8 (by omega)).2 =
      (scanAt block 0 8 (by omega)).2 := by
  have hfix : wordPerm σ (Fin.last modulus) = Fin.last modulus :=
    wordPerm_fixes_sentinel σ
  have hpoint (j : Fin 8) :
      (splitBlock31Equiv (blockPerm σ block)).2 j =
        wordPerm σ ((splitBlock31Equiv block).2 j) := by
    rw [splitBlock31_blockPerm]
    rfl
  rw [scanAt, blockSuffix_full, sourceScan_countScan modulus _ (by rfl)]
  rw [scanAt, blockSuffix_full, sourceScan_countScan modulus _ (by rfl)]
  rw [words31_value, words31_value]
  have hfun : (fun j : Fin 8 => ((splitBlock31Equiv (blockPerm σ block)).2 j).val) =
      fun j => (wordPerm σ ((splitBlock31Equiv block).2 j)).val := by
    funext j
    exact congrArg Fin.val (hpoint j)
  rw [show List.ofFn (fun j : Fin 8 =>
      ((splitBlock31Equiv (blockPerm σ block)).2 j).val) =
      List.ofFn (fun j : Fin 8 =>
        (wordPerm σ ((splitBlock31Equiv block).2 j)).val) from congrArg List.ofFn hfun]
  exact (countScan_ofFn_perm (p := modulus) (n := 8)
    (e := wordPerm σ) hfix
    ((splitBlock31Equiv block).2)).symm

#print axioms sourceScan_countScan
#print axioms countScan_perm_fix_sentinel
#print axioms countScan_ofFn_perm
#print axioms scanAt_count_blockPerm
end AspisV8R19.R451BlockStoppingPermutation
