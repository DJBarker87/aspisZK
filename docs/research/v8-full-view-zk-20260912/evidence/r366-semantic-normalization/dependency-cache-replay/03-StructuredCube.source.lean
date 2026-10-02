import AspisV8R17.StructuredRound
import AspisV8R17.CausalRounds

/-! The proposed mask has the required sumcheck recurrence for every
number of rounds. This is not an assertion that V8 implements this mask. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [Field F] [NeZero (2 : F)] {width : ℕ}

def cubeSum : (r : ℕ) → (RoundCoins F r → F) → F
  | 0, f => f PUnit.unit
  | r+1, f => cubeSum r (fun z => f (0,z)) + cubeSum r (fun z => f (1,z))

def structuredMask : (r : ℕ) → F → RoundCoins (F × (Fin width → F)) r →
    RoundCoins F r → F
  | 0, carry, _, _ => carry
  | r+1, carry, coins, z => structuredMask r
      (semanticRound carry coins.1.1 coins.1.2 z.1) coins.2 z.2

theorem structuredMask_cube_sum (r : ℕ) (carry : F)
    (coins : RoundCoins (F × (Fin width → F)) r) :
    cubeSum r (structuredMask r carry coins) = carry := by
  induction r generalizing carry with
  | zero => rfl
  | succ r ih =>
    simp only [cubeSum, structuredMask, ih]
    exact semanticRound_boundary carry coins.1.1 coins.1.2

/-- After any prefix has updated the carry, the next round polynomial is
exactly half that carry plus its zero-boundary polynomial. -/
theorem structuredMask_suffix_round (r : ℕ) (carry a : F) (b : Fin width → F)
    (coins : RoundCoins (F × (Fin width → F)) r) (x : F) :
    cubeSum r (fun z => structuredMask (r+1) carry ((a,b),coins) (x,z)) =
      semanticRound carry a b x := by
  exact structuredMask_cube_sum r (semanticRound carry a b x) coins

#print axioms structuredMask_cube_sum
#print axioms structuredMask_suffix_round
end AspisV8R17
