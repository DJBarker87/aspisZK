import AspisV8R17.StructuredCube

/-! Exact algebra of the reverse weighted accumulation used by Rust
`mask_eval`. Array/index/field implementation refinement is separate. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [Field F]

/-- Recursive description of processing contributions from last to first:
add contribution*scale, then multiply scale by half. -/
def reverseMaskAccumulator (half : F) : List F → F × F
  | [] => (0, 1)
  | x :: xs =>
    let tail := reverseMaskAccumulator half xs
    (tail.1 + x * tail.2, tail.2 * half)

def sourceMaskLoop (half carry : F) (contributions : List F) : F :=
  let result := reverseMaskAccumulator half contributions
  result.1 + carry * result.2

/-- Literal reverse iterator with the source's two-variable loop state. -/
theorem reverseMaskAccumulator_eq_reverse_fold (half : F) (xs : List F) :
    reverseMaskAccumulator half xs = xs.reverse.foldl
      (fun acc x => (acc.1 + x * acc.2, acc.2 * half)) (0, 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons,
      List.foldl_nil, reverseMaskAccumulator, ih]

theorem sourceMaskLoop_nil (half carry : F) :
    sourceMaskLoop half carry [] = carry := by
  simp [sourceMaskLoop, reverseMaskAccumulator]

theorem sourceMaskLoop_cons (half carry x : F) (xs : List F) :
    sourceMaskLoop half carry (x :: xs) =
      sourceMaskLoop half (carry * half + x) xs := by
  simp only [sourceMaskLoop, reverseMaskAccumulator]
  ring

theorem reverseMaskAccumulator_scale (half : F) (xs : List F) :
    (reverseMaskAccumulator half xs).2 = half ^ xs.length := by
  induction xs with
  | nil => simp [reverseMaskAccumulator]
  | cons x xs ih => simp [reverseMaskAccumulator, ih, pow_succ]

/-- The contributions use the same per-round zero-boundary polynomial as
the existing cube theorem, in first-to-last round order. -/
def maskContributions {width : ℕ} : (r : ℕ) →
    RoundCoins (F × (Fin width → F)) r → RoundCoins F r → List F
  | 0, _, _ => []
  | r+1, coins, z => roundEval coins.1.1 coins.1.2 z.1 ::
      maskContributions r coins.2 z.2

theorem sourceMaskLoop_eq_structuredMask [NeZero (2 : F)] {width : ℕ}
    (r : ℕ) (carry : F) (coins : RoundCoins (F × (Fin width → F)) r)
    (z : RoundCoins F r) :
    sourceMaskLoop (1 / 2) carry (maskContributions r coins z) =
      structuredMask r carry coins z := by
  induction r generalizing carry with
  | zero => simp [maskContributions, sourceMaskLoop_nil, structuredMask]
  | succ r ih =>
    simp only [maskContributions, sourceMaskLoop_cons, structuredMask]
    simpa [semanticRound, div_eq_mul_inv] using
      ih (carry * (1 / 2) + roundEval coins.1.1 coins.1.2 z.1) coins.2 z.2

theorem sourceMaskLoop_cube_sum [NeZero (2 : F)] {width : ℕ}
    (r : ℕ) (carry : F) (coins : RoundCoins (F × (Fin width → F)) r) :
    cubeSum r (fun z => sourceMaskLoop (1 / 2) carry
      (maskContributions r coins z)) = carry := by
  simp only [sourceMaskLoop_eq_structuredMask]
  exact structuredMask_cube_sum r carry coins

theorem sourceMaskLoop_suffix_round [NeZero (2 : F)] {width : ℕ}
    (r : ℕ) (carry a : F) (b : Fin width → F)
    (coins : RoundCoins (F × (Fin width → F)) r) (x : F) :
    cubeSum r (fun z => sourceMaskLoop (1 / 2) carry
      (maskContributions (r+1) ((a,b),coins) (x,z))) =
      semanticRound carry a b x := by
  simp only [sourceMaskLoop_eq_structuredMask]
  exact structuredMask_suffix_round r carry a b coins x

#print axioms reverseMaskAccumulator_eq_reverse_fold
#print axioms sourceMaskLoop_cons
#print axioms reverseMaskAccumulator_scale
#print axioms sourceMaskLoop_eq_structuredMask
#print axioms sourceMaskLoop_cube_sum
#print axioms sourceMaskLoop_suffix_round
end AspisV8R17
