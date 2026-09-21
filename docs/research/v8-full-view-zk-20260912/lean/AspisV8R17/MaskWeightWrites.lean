import AspisV8R17.ConsecutiveWrites
import AspisV8R17.MaskSourceSlices

/-! Mutation model of the reverse mask_weights table writes. The source
field operations and Rust execution refinement remain explicit boundaries. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [Field F]

def reverseMaskTable (width : ℕ) (half : F) : (r : ℕ) → RoundCoins F r →
    ℕ → (ℕ → F) → (ℕ → F) × F
  | 0, _, _, table => (table,1)
  | r+1, z, start, table =>
      let tail := reverseMaskTable width half r z.2 (start+(width+1)) table
      let block := tail.2*(1-(z.1+z.1)) :: powerWeightLoop tail.2 z.1 width (z.1^2)
      (writeConsecutive block start tail.1, tail.2*half)

theorem reverseMaskTable_eq (width : ℕ) (half : F) (r : ℕ) (z : RoundCoins F r)
    (start : ℕ) (table : ℕ → F) :
    reverseMaskTable width half r z start table =
      (writeConsecutive (reverseWeightBlocks width half r z).1 start table,
        (reverseWeightBlocks width half r z).2) := by
  induction r generalizing start table with
  | zero => rfl
  | succ r ih =>
    simp only [reverseMaskTable, ih, reverseWeightBlocks, literal_round_weight_block]
    apply Prod.ext
    · dsimp only
      rw [writeConsecutive_append]
      simpa only [roundWeightBlock_length] using
        writeConsecutive_adjacent_commute
          (roundWeightBlock width (reverseWeightBlocks width half r z.2).2 z.1)
          (reverseWeightBlocks width half r z.2).1 start table
    · rfl

def sourceMaskTable (half : F) (z : RoundCoins F 10) (table : ℕ → F) : ℕ → F :=
  let result := reverseMaskTable 26 half 10 z 1 table
  Function.update result.1 0 result.2

theorem sourceMaskTable_eq_writes (half : F) (z : RoundCoins F 10) (table : ℕ → F) :
    sourceMaskTable half z table = writeConsecutive (flatMaskWeights 26 half 10 z) 0 table := by
  unfold sourceMaskTable
  rw [reverseMaskTable_eq]
  have h := writeConsecutive_adjacent_commute
    [(reverseWeightBlocks 26 half 10 z).2] (reverseWeightBlocks 26 half 10 z).1 0 table
  simpa only [flatMaskWeights, writeConsecutive, List.length_singleton, Nat.zero_add] using h

theorem sourceMaskTable_entry (half : F) (z : RoundCoins F 10) (table : ℕ → F) (i : Fin 271) :
    sourceMaskTable half z table i.val = maskWeights271 half z i := by
  rw [sourceMaskTable_eq_writes]
  have hlen : (flatMaskWeights 26 half 10 z).length=271 := by
    simpa using flatMaskWeights_length 26 half 10 z
  have h := writeConsecutive_inside (flatMaskWeights 26 half 10 z) 0 table i.val (by omega)
  simpa only [Nat.zero_add, maskWeights271, listAsFin, List.get_eq_getElem] using h

theorem sourceMaskTable_outside (half : F) (z : RoundCoins F 10) (table : ℕ → F)
    (j : ℕ) (hj : 271≤j) : sourceMaskTable half z table j = table j := by
  rw [sourceMaskTable_eq_writes]
  apply writeConsecutive_outside
  right
  simpa only [flatMaskWeights_length] using hj

theorem mask_weight_address_bounds (r i : ℕ) (hr : r<10) (hi : i<27) :
    0<1+27*r+i ∧ 1+27*r+i<271 := by omega

theorem mask_weight_address_injective (r s i j : ℕ) (hi : i<27) (hj : j<27)
    (same : 1+27*r+i=1+27*s+j) : r=s ∧ i=j := by omega

theorem source_written_mask_pairing (half : F) (m : Fin 1024 → F)
    (z : RoundCoins F 10) (table : ℕ → F) :
    (∑ i, sourceMixedWeight (fun j : Fin 271 => sourceMaskTable half z table j.val) i*m i) =
      sourceMaskLoop half (mixedSourceCoins m 0)
        (literalMaskContributions 10 (readRoundCoins 26 (mixedSourceCoins m) 10 1) z) := by
  have hw : (fun j : Fin 271 => sourceMaskTable half z table j.val) = maskWeights271 half z := by
    funext j
    exact sourceMaskTable_entry half z table j
  rw [hw]
  exact source_mask_weights_pairing half m z

#print axioms reverseMaskTable_eq
#print axioms sourceMaskTable_eq_writes
#print axioms sourceMaskTable_entry
#print axioms sourceMaskTable_outside
#print axioms mask_weight_address_bounds
#print axioms mask_weight_address_injective
#print axioms source_written_mask_pairing
end AspisV8R17
