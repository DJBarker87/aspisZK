import AspisV8R17.MaskWeightVector

/-! Source slice addresses: carry at zero, followed by ten 27-entry blocks.
This discharges the flat-coordinate premise without resampling any entry. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [Field F]

def readRoundCoins (width : ℕ) (values : ℕ → F) : (r : ℕ) → ℕ →
    RoundCoins (F × (Fin width → F)) r
  | 0, _ => PUnit.unit
  | r+1, start =>
      ((values start, fun i => values (start+1+i.val)),
        readRoundCoins width values r (start+(width+1)))

theorem flatten_readRoundCoins (width r : ℕ) (values : ℕ → F) (start : ℕ) :
    flattenRoundCoins r (readRoundCoins width values r start) =
      List.ofFn (fun i : Fin (r*(width+1)) => values (start+i.val)) := by
  induction r generalizing start with
  | zero => simp [readRoundCoins, flattenRoundCoins]
  | succ r ih =>
    simp only [readRoundCoins, flattenRoundCoins, roundCoinBlock, ih]
    conv_rhs => rw [show (r+1)*(width+1)=(width+1)+r*(width+1) by ring,
      List.ofFn_add, List.ofFn_succ]
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem read_mask_flat_list (values : ℕ → F) :
    values 0 :: flattenRoundCoins 10 (readRoundCoins 26 values 10 1) =
      List.ofFn (fun i : Fin 271 => values i.val) := by
  rw [flatten_readRoundCoins]
  conv_rhs => rw [List.ofFn_succ]
  change values 0 :: List.ofFn (fun i : Fin 270 => values (1+i.val)) =
    values 0 :: List.ofFn (fun i : Fin 270 => values (i.val+1))
  have hf : (fun i : Fin 270 => values (1+i.val)) = (fun i : Fin 270 => values (i.val+1)) := by
    funext i
    rw [Nat.add_comm]
  rw [hf]

theorem maskCoins271_reads (values : ℕ → F) (i : Fin 271) :
    maskCoins271 (values 0) (readRoundCoins 26 values 10 1) i = values i.val := by
  unfold maskCoins271 listAsFin
  simp only [List.get_eq_getElem]
  simp only [read_mask_flat_list, List.getElem_ofFn]

def mixedSourceCoins (m : Fin 1024 → F) (i : ℕ) : F :=
  sourceMixHorner ((i+1 : ℕ) : F) (List.ofFn m)

theorem source_mask_weights_pairing (half : F) (m : Fin 1024 → F) (z : RoundCoins F 10) :
    (∑ i, sourceMixedWeight (maskWeights271 half z) i*m i) =
      sourceMaskLoop half (mixedSourceCoins m 0)
        (literalMaskContributions 10 (readRoundCoins 26 (mixedSourceCoins m) 10 1) z) := by
  apply mixed_mask_weights_pairing
  intro i
  exact (maskCoins271_reads (mixedSourceCoins m) i).symm

theorem source_original_mask_weight_dot (half : F) (points : Fin 3 → Fin 10 → F)
    (kappa : F) (inactive : Finset (Fin 1024)) (m : Fin 1024 → F) (z : RoundCoins F 10) :
    (∑ i, sourceOriginalWeight points kappa inactive
      (sourceMixedWeight (maskWeights271 half z)) true i*m i) =
      kappa*sourceMaskLoop half (mixedSourceCoins m 0)
        (literalMaskContributions 10 (readRoundCoins 26 (mixedSourceCoins m) 10 1) z) +
      kappa^2*sourcePointFunctional (points 1) m +
      kappa^3*sourcePointFunctional (points 2) m + ∑ i ∈ inactive, m i := by
  rw [sourceOriginalWeight_dot]
  simp only [if_true, source_mask_weights_pairing]

#print axioms flatten_readRoundCoins
#print axioms read_mask_flat_list
#print axioms maskCoins271_reads
#print axioms source_mask_weights_pairing
#print axioms source_original_mask_weight_dot
end AspisV8R17
