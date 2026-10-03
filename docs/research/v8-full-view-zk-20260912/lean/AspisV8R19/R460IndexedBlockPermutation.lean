import AspisV8R19.R459IndexedFiniteTape
import AspisV8R19.R461OptionScanCount
import AspisV8R19.R457IndexedScan
import AspisV8R19.R447SourceInitialBlockLaw

set_option autoImplicit false
namespace AspisV8R19.R460IndexedBlockPermutation
open R421UniformMasked31Block R442RejectionAlphabet R443BoundedRejectionMass
open R445InitialBlockRejectionLaw R444InitialSourceLimb
open R449BlockPermutation R451BlockStoppingPermutation
open R456IndexedWordPermutation R457IndexedScan R459IndexedFiniteTape R461OptionScanCount
noncomputable section

def decodedBlockEquiv : SourceDuplexStep.State ≃ ((Fin 8 → Fin 2) × Tape modulus 8) :=
  splitBlock31Equiv.trans
    (Equiv.prodCongr (Equiv.refl _) (decodeTapeEquiv modulus 8))

def indexedBlockPerm (σ : Nat → Equiv.Perm (Fin modulus)) (offset : Nat) :
    SourceDuplexStep.State ≃ SourceDuplexStep.State :=
  decodedBlockEquiv.trans ((Equiv.prodCongr (Equiv.refl _)
    (finiteTapeEquiv σ offset 8)).trans decodedBlockEquiv.symm)

theorem decodedBlock_perm (σ : Nat → Equiv.Perm (Fin modulus)) (offset : Nat)
    (block : SourceDuplexStep.State) :
    decodedBlockEquiv (indexedBlockPerm σ offset block) =
      Equiv.prodCongr (Equiv.refl _) (finiteTapeEquiv σ offset 8)
        (decodedBlockEquiv block) := by
  simp only [indexedBlockPerm, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem result_decoded (block : SourceDuplexStep.State) :
    initialBlockResult block = run 8 (decodedBlockEquiv block).2 := rfl

theorem indexedBlock_result (σ : Nat → Equiv.Perm (Fin modulus)) (offset : Nat)
    (block : SourceDuplexStep.State) :
    initialBlockResult (indexedBlockPerm σ offset block) =
      Option.map (σ offset) (initialBlockResult block) := by
  rw [result_decoded, result_decoded, decodedBlock_perm]
  change run 8 (transformTape σ offset 8 (decodedBlockEquiv block).2) = _
  rw [R446RejectionListExecution.run_list, ofFn_transformTape,
    firstAccepted_transform, ← R446RejectionListExecution.run_list]

theorem decodeTape_list {p n : Nat} (w : Fin n → Fin (p+1)) :
    (List.ofFn w).map (alphabetDecode p) = List.ofFn (decodeTapeEquiv p n w) := by
  rw [List.map_ofFn]
  rfl

theorem count_decoded (block : SourceDuplexStep.State) :
    (scanAt block 0 8 (by omega)).2 = optionCount (List.ofFn (decodedBlockEquiv block).2) := by
  rw [scanAt, blockSuffix_full, sourceScan_countScan modulus _ rfl]
  have hm : SamplerWords.words 31 block =
      (List.ofFn ((splitBlock31Equiv block).2)).map Fin.val := by
    rw [words31_value]
    exact (List.map_ofFn (f := (splitBlock31Equiv block).2) (g := Fin.val)).symm
  rw [hm]
  calc
    _ = optionCount ((List.ofFn ((splitBlock31Equiv block).2)).map
        (alphabetDecode modulus)) :=
      countScan_map_val_eq_optionCount (p := modulus) (List.ofFn ((splitBlock31Equiv block).2))
    _ = _ := by
      rw [decodeTape_list]
      rfl

theorem indexedBlock_count (σ : Nat → Equiv.Perm (Fin modulus)) (offset : Nat)
    (block : SourceDuplexStep.State) :
    (scanAt (indexedBlockPerm σ offset block) 0 8 (by omega)).2 =
      (scanAt block 0 8 (by omega)).2 := by
  rw [count_decoded, count_decoded, decodedBlock_perm]
  change optionCount (List.ofFn (transformTape σ offset 8 (decodedBlockEquiv block).2)) = _
  rw [ofFn_transformTape, transform_optionCount]

#print axioms decodedBlock_perm
#print axioms result_decoded
#print axioms indexedBlock_result
#print axioms decodeTape_list
#print axioms count_decoded
#print axioms indexedBlock_count
end
end AspisV8R19.R460IndexedBlockPermutation
