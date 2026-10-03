import AspisV8R19.R451BlockStoppingCore
import AspisV8R19.R449BlockPermutation

set_option autoImplicit false
namespace AspisV8R19.R451BlockStoppingPermutation
open AspisV8R19.R444InitialSourceLimb
open AspisV8R19.SamplerWords
open AspisV8R19.R421UniformMasked31Block
open AspisV8R19.R442RejectionAlphabet
open AspisV8R19.R445InitialBlockRejectionLaw
open AspisV8R19.R449BlockPermutation

attribute [local irreducible] AspisV8R19.R449BlockPermutation.blockPerm
  AspisV8R19.R421UniformMasked31Block.splitBlock31Equiv

theorem scanAt_count_words (block : AspisV8R19.SourceDuplexStep.State) :
    (scanAt block 0 8 (by omega)).2 = countScan modulus (words 31 block) := by
  rw [scanAt, blockSuffix_full, sourceScan_countScan modulus _ (by rfl), words31_value]

theorem prod_second {A B I : Type} (e : B ≃ B) (q : A × (I → B)) :
    (Equiv.prodCongr (Equiv.refl A) (Equiv.piCongrRight (fun _ => e)) q).2 =
      fun j => e (q.2 j) := rfl

theorem words31_blockPerm (σ : Equiv.Perm (Fin modulus))
    (block : AspisV8R19.SourceDuplexStep.State) :
    words 31 (blockPerm σ block) =
      List.ofFn (fun j : Fin 8 => (wordPerm σ ((splitBlock31Equiv block).2 j)).val) := by
  have hp := congrArg
    (fun q : (Fin 8 → Fin 2) × (Fin 8 → Fin (2^31)) => q.2)
    (splitBlock31_blockPerm σ block)
  have hs := prod_second (A := Fin 8 → Fin 2) (I := Fin 8)
    (wordPerm σ) (splitBlock31Equiv block)
  have hproj : (splitBlock31Equiv (blockPerm σ block)).2 =
      fun j => wordPerm σ ((splitBlock31Equiv block).2 j) := hp.trans hs
  calc
    _ = List.ofFn (fun j => ((splitBlock31Equiv (blockPerm σ block)).2 j).val) :=
      words31_value (blockPerm σ block)
    _ = _ := congrArg
      (fun w : Fin 8 → Fin (2^31) => List.ofFn (fun j => (w j).val)) hproj

theorem scanAt_count_blockPerm (σ : Equiv.Perm (Fin modulus))
    (block : AspisV8R19.SourceDuplexStep.State) :
    (scanAt (blockPerm σ block) 0 8 (by omega)).2 =
      (scanAt block 0 8 (by omega)).2 := by
  have hfix : wordPerm σ (Fin.last modulus) = Fin.last modulus :=
    wordPerm_fixes_sentinel σ
  rw [scanAt_count_words, scanAt_count_words, words31_blockPerm, words31_value]
  exact (countScan_ofFn_perm (p := modulus) (n := 8)
    (e := wordPerm σ) hfix
    ((splitBlock31Equiv block).2)).symm

#print axioms sourceScan_countScan
#print axioms countScan_perm_fix_sentinel
#print axioms countScan_ofFn_perm
#print axioms scanAt_count_words
#print axioms words31_blockPerm
#print axioms scanAt_count_blockPerm
end AspisV8R19.R451BlockStoppingPermutation
