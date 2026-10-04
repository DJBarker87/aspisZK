import AspisV8R19.R578FiniteWordTape
import AspisV8R19.R445InitialBlockRejectionLaw

set_option autoImplicit false
namespace AspisV8R19.R579FourBlockTape
open R421UniformMasked31Block R442RejectionAlphabet R443BoundedRejectionMass
open R445InitialBlockRejectionLaw R572SequentialWordMass R578FiniteWordTape
open OracleResampling SourceDuplexStep SamplerWords
noncomputable section

abbrev Blocks := Fin 4 → State
abbrev High := Fin 4 → Fin 8 → Fin 2
abbrev Low := Fin 4 → Fin 8 → Fin (2^31)

def splitBlocks : Blocks ≃ High × Low where
  toFun b := (fun i => (splitBlock31Equiv (b i)).1,
    fun i => (splitBlock31Equiv (b i)).2)
  invFun q i := splitBlock31Equiv.symm (q.1 i,q.2 i)
  left_inv b := by
    funext i
    exact splitBlock31Equiv.symm_apply_apply (b i)
  right_inv q := by
    apply Prod.ext
    · funext i j
      exact congrArg (fun z => z.1 j) (splitBlock31Equiv.apply_symm_apply (q.1 i,q.2 i))
    · funext i j
      exact congrArg (fun z => z.2 j) (splitBlock31Equiv.apply_symm_apply (q.1 i,q.2 i))

def uncurryLow : Low ≃ (Fin 4 × Fin 8 → Fin (2^31)) where
  toFun b q := b q.1 q.2
  invFun f i j := f (i,j)
  left_inv _ := rfl
  right_inv _ := rfl

def lowTapeEquiv : Low ≃ Tape modulus 32 :=
  uncurryLow.trans (Equiv.arrowCongr (finProdFinEquiv (m := 4) (n := 8))
    (alphabetEquiv modulus))

def blockTape (blocks : Blocks) : Tape modulus 32 :=
  lowTapeEquiv (splitBlocks blocks).2

theorem blockTape_value (blocks : Blocks) (i : Fin 32) :
    ((alphabetEquiv modulus).symm (blockTape blocks i)).val =
      masked 31 (word (blocks ((finProdFinEquiv (m := 4) (n := 8)).symm i).1)
        ((finProdFinEquiv (m := 4) (n := 8)).symm i).2) := by
  change ((alphabetEquiv modulus).symm ((alphabetEquiv modulus)
    ((splitBlock31Equiv (blocks ((finProdFinEquiv (m := 4) (n := 8)).symm i).1)).2
      ((finProdFinEquiv (m := 4) (n := 8)).symm i).2))).val = _
  rw [Equiv.symm_apply_apply]
  exact masked31_value _ _

theorem four_block_projection (f : Tape modulus 32 → ℚ) :
    mean (fun blocks : Blocks => f (blockTape blocks)) = mean f := by
  unfold blockTape
  rw [mean_equiv splitBlocks (fun q => f (lowTapeEquiv q.2))]
  rw [mean_prod (fun (_ : High) (low : Low) => f (lowTapeEquiv low))]
  rw [mean_const]
  exact mean_equiv lowTapeEquiv f

theorem four_block_tuple_mass (target : Fin 4 → Fin modulus) (cursor : Nat) :
    mean (fun blocks : Blocks =>
      observeTape (observedList (List.ofFn target))
        (runTape 32 (limbs 8 4 cursor) (blockTape blocks))) =
      ((1-(1/(2147483648 : ℚ))^8)/2147483647)^4 := by
  rw [four_block_projection]
  simpa only [modulus, Nat.cast_ofNat,
    show (2147483647 : ℚ)+1=2147483648 by norm_num] using
    finite_tuple_mass (p := modulus) (by decide) 8 4 cursor target

#print axioms splitBlocks
#print axioms lowTapeEquiv
#print axioms blockTape_value
#print axioms four_block_projection
#print axioms four_block_tuple_mass
end
end AspisV8R19.R579FourBlockTape
