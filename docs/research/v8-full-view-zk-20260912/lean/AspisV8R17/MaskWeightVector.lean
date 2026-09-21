import AspisV8R17.MaskWeightBlocks
import AspisV8R17.SourceMixingWeights

/-! Inner power-loop weights and the full 271-entry finite interface.
No list zip/truncation or discarded carry coordinate enters the pairing. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [Field F]

def powerWeightLoop (scale x : F) : ℕ → F → List F
  | 0, _ => []
  | n+1, power => scale*(power-x) :: powerWeightLoop scale x n (power*x)

theorem powerWeightLoop_closed (scale x : F) (n k : ℕ) :
    powerWeightLoop scale x n (x^k) =
      List.ofFn (fun i : Fin n => scale*(x^(k+i.val)-x)) := by
  induction n generalizing k with
  | zero => simp [powerWeightLoop]
  | succ n ih =>
    rw [powerWeightLoop, ← pow_succ, ih, List.ofFn_succ]
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem literal_round_weight_block (width : ℕ) (scale x : F) :
    scale*(1-(x+x)) :: powerWeightLoop scale x width (x^2) =
      roundWeightBlock width scale x := by
  simp only [powerWeightLoop_closed, roundWeightBlock, Nat.add_comm 2]

def listAsFin (n : ℕ) (xs : List F) (h : xs.length=n) (i : Fin n) : F :=
  xs.get ⟨i.val, by omega⟩

theorem listAsFin_ofFn (n : ℕ) (xs : List F) (h : xs.length=n) :
    List.ofFn (listAsFin n xs h) = xs := by
  subst n
  exact List.ofFn_get xs

def maskWeights271 (half : F) (z : RoundCoins F 10) : Fin 271 → F :=
  listAsFin 271 (flatMaskWeights 26 half 10 z) (by
    simpa using flatMaskWeights_length 26 half 10 z)

def maskCoins271 (carry : F) (coins : RoundCoins (F × (Fin 26 → F)) 10) : Fin 271 → F :=
  listAsFin 271 (carry::flattenRoundCoins 10 coins) (by simp [flattenRoundCoins_length])

theorem maskWeights271_dot (half carry : F)
    (coins : RoundCoins (F × (Fin 26 → F)) 10) (z : RoundCoins F 10) :
    (∑ i, maskWeights271 half z i * maskCoins271 carry coins i) =
      sourceMaskLoop half carry (literalMaskContributions 10 coins z) := by
  rw [← maskListDot_ofFn]
  unfold maskWeights271 maskCoins271
  rw [listAsFin_ofFn, listAsFin_ofFn, flatMaskWeights_dot]

theorem maskWeights271_structuredMask [NeZero (2 : F)] (carry : F)
    (coins : RoundCoins (F × (Fin 26 → F)) 10) (z : RoundCoins F 10) :
    (∑ i, maskWeights271 (1/2) z i * maskCoins271 carry coins i) =
      structuredMask 10 carry coins z := by
  rw [maskWeights271_dot, literalMaskLoop_eq_structuredMask]

/-- The only remaining link in this composition is identified explicitly:
the tuple of source slices must flatten to the already-computed Horner coins.
This is an equality premise, not fresh randomness or a hiding assumption. -/
theorem mixed_mask_weights_pairing (half carry : F) (m : Fin 1024 → F)
    (coins : RoundCoins (F × (Fin 26 → F)) 10) (z : RoundCoins F 10)
    (slices : ∀ i : Fin 271, sourceMixHorner ((i.val+1 : ℕ) : F) (List.ofFn m) =
      maskCoins271 carry coins i) :
    (∑ i, sourceMixedWeight (maskWeights271 half z) i * m i) =
      sourceMaskLoop half carry (literalMaskContributions 10 coins z) := by
  rw [sourceMixedWeight_dot]
  simp only [slices]
  exact maskWeights271_dot half carry coins z

#print axioms powerWeightLoop_closed
#print axioms literal_round_weight_block
#print axioms listAsFin_ofFn
#print axioms maskWeights271_dot
#print axioms maskWeights271_structuredMask
#print axioms mixed_mask_weights_pairing
end AspisV8R17
