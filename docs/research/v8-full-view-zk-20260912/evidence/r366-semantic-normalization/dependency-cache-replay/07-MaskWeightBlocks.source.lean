import AspisV8R17.SourceZeroBoundary

/-! Flat round blocks for mask_weights. Dot products have explicit matching
lengths; the 27-entry block and reverse-round carry scale are not omitted. -/
set_option autoImplicit false
namespace AspisV8R17
open scoped BigOperators
variable {F : Type*} [Field F]

def maskListDot : List F → List F → F
  | x::xs, y::ys => x*y+maskListDot xs ys
  | _, _ => 0

theorem maskListDot_append (xs ys us vs : List F) (h : xs.length=ys.length) :
    maskListDot (xs++us) (ys++vs) = maskListDot xs ys+maskListDot us vs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [maskListDot]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [maskListDot, ih ys h, add_assoc]

theorem maskListDot_ofFn (n : ℕ) (a b : Fin n → F) :
    maskListDot (List.ofFn a) (List.ofFn b) = ∑ i, a i*b i := by
  induction n with
  | zero => simp [maskListDot]
  | succ n ih => simp [List.ofFn_succ, maskListDot, ih, Fin.sum_univ_succ]

def roundWeightBlock (width : ℕ) (scale x : F) : List F :=
  scale*(1-(x+x)) :: List.ofFn (fun i : Fin width => scale*(x^(i.val+2)-x))

def roundCoinBlock {width : ℕ} (u : F × (Fin width → F)) : List F :=
  u.1 :: List.ofFn u.2

theorem roundWeightBlock_length (width : ℕ) (scale x : F) :
    (roundWeightBlock width scale x).length = width+1 := by simp [roundWeightBlock]

theorem roundCoinBlock_length {width : ℕ} (u : F × (Fin width → F)) :
    (roundCoinBlock u).length = width+1 := by simp [roundCoinBlock]

theorem roundWeightBlock_dot {width : ℕ} (scale x : F) (u : F × (Fin width → F)) :
    maskListDot (roundWeightBlock width scale x) (roundCoinBlock u) =
      scale*sourceZeroBoundary u.1 u.2 x := by
  simp only [roundWeightBlock, roundCoinBlock, maskListDot, maskListDot_ofFn,
    sourceZeroBoundary_eq_roundEval, roundEval, mul_add, Finset.mul_sum]
  have hsum : (∑ i, scale*(x^(i.val+2)-x)*u.2 i) =
      ∑ i, scale*(u.2 i*(x^(i.val+2)-x)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

def flattenRoundCoins {width : ℕ} : (r : ℕ) →
    RoundCoins (F × (Fin width → F)) r → List F
  | 0, _ => []
  | r+1, coins => roundCoinBlock coins.1 ++ flattenRoundCoins r coins.2

def reverseWeightBlocks (width : ℕ) (half : F) : (r : ℕ) → RoundCoins F r → List F × F
  | 0, _ => ([],1)
  | r+1, z =>
      let tail := reverseWeightBlocks width half r z.2
      (roundWeightBlock width tail.2 z.1 ++ tail.1, tail.2*half)

theorem flattenRoundCoins_length {width : ℕ} (r : ℕ)
    (coins : RoundCoins (F × (Fin width → F)) r) :
    (flattenRoundCoins r coins).length = r*(width+1) := by
  induction r with
  | zero => simp [flattenRoundCoins]
  | succ r ih => simp [flattenRoundCoins, roundCoinBlock_length, ih, Nat.add_mul, Nat.add_comm]

theorem reverseWeightBlocks_length (width : ℕ) (half : F) (r : ℕ) (z : RoundCoins F r) :
    (reverseWeightBlocks width half r z).1.length = r*(width+1) := by
  induction r with
  | zero => simp [reverseWeightBlocks]
  | succ r ih => simp [reverseWeightBlocks, roundWeightBlock_length, ih, Nat.add_mul, Nat.add_comm]

theorem reverseWeightBlocks_scale (width : ℕ) (half : F) (r : ℕ) (z : RoundCoins F r) :
    (reverseWeightBlocks width half r z).2 = half^r := by
  induction r with
  | zero => simp [reverseWeightBlocks]
  | succ r ih => simp [reverseWeightBlocks, ih, pow_succ]

def flatMaskWeights (width : ℕ) (half : F) (r : ℕ) (z : RoundCoins F r) : List F :=
  let blocks := reverseWeightBlocks width half r z
  blocks.2 :: blocks.1

theorem flatMaskWeights_length (width : ℕ) (half : F) (r : ℕ) (z : RoundCoins F r) :
    (flatMaskWeights width half r z).length = 1+r*(width+1) := by
  simp [flatMaskWeights, reverseWeightBlocks_length, Nat.add_comm]

theorem flatMaskWeights_dot {width : ℕ} (half carry : F) (r : ℕ)
    (coins : RoundCoins (F × (Fin width → F)) r) (z : RoundCoins F r) :
    maskListDot (flatMaskWeights width half r z) (carry::flattenRoundCoins r coins) =
      sourceMaskLoop half carry (literalMaskContributions r coins z) := by
  induction r generalizing carry with
  | zero => simp [flatMaskWeights, reverseWeightBlocks, flattenRoundCoins,
      literalMaskContributions, maskListDot, sourceMaskLoop_nil]
  | succ r ih =>
    simp only [flatMaskWeights, reverseWeightBlocks, flattenRoundCoins, maskListDot,
      literalMaskContributions, sourceMaskLoop_cons]
    rw [maskListDot_append _ _ _ _ (by rw [roundWeightBlock_length, roundCoinBlock_length]),
      roundWeightBlock_dot]
    have ht := ih (carry*half+sourceZeroBoundary coins.1.1 coins.1.2 z.1) coins.2 z.2
    simp only [flatMaskWeights, maskListDot] at ht
    rw [← ht]
    ring

theorem flatMaskWeights_structuredMask [NeZero (2 : F)] {width : ℕ} (carry : F) (r : ℕ)
    (coins : RoundCoins (F × (Fin width → F)) r) (z : RoundCoins F r) :
    maskListDot (flatMaskWeights width (1/2) r z) (carry::flattenRoundCoins r coins) =
      structuredMask r carry coins z := by
  rw [flatMaskWeights_dot, literalMaskLoop_eq_structuredMask]

#print axioms roundWeightBlock_dot
#print axioms reverseWeightBlocks_length
#print axioms reverseWeightBlocks_scale
#print axioms flatMaskWeights_length
#print axioms flatMaskWeights_dot
#print axioms flatMaskWeights_structuredMask
end AspisV8R17
