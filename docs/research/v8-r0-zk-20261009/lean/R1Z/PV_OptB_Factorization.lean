import R1Z.PV_RunJoin_OsWorld
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_Factorization

/-- Exact public-factorization condition. The signal includes the reached
call's family, position and exact error. The OS world is a fixed input,
not a witness-indexed scheduler. `none` records that no failure is reached. -/
def Independent {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event) : Prop :=
  ∀ w u, pub w = pub u → ∀ os coins, signal w os coins = signal u os coins

/-- A public decoder proves independence without restricting the observer. -/
theorem independent_of_public_decoder {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (decoder : Public → World → Coins → Option Event)
    (law : ∀ w os coins, signal w os coins = decoder (pub w) os coins) :
    Independent pub signal := by
  intro w u same os coins
  rw [law,law,same]

/-- Conversely, fiberwise independence supplies a decoder, including on
public inputs with no admitted witness. No witness enters its signature.
The proof obligation remains equality of *actual reached observations*. -/
theorem public_decoder_of_independent {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (independent : Independent pub signal) :
    ∃ decoder : Public → World → Coins → Option Event,
      ∀ w os coins, signal w os coins = decoder (pub w) os coins := by
  classical
  let decoder := fun p os coins =>
    if inhabited : ∃ w, pub w = p then
      signal (Classical.choose inhabited) os coins
    else none
  refine ⟨decoder,?_⟩
  intro w os coins
  dsimp only [decoder]
  rw [dif_pos ⟨w,rfl⟩]
  exact independent w (Classical.choose (show ∃ u, pub u = pub w from ⟨w,rfl⟩))
    (Classical.choose_spec (show ∃ u, pub u = pub w from ⟨w,rfl⟩)).symm os coins

/-- A differing reached failure observation is the exact refutation needed
by D215, provided w and u are admitted deployed witnesses with equal public
inputs. A conditional body/retry example alone does not supply those facts. -/
theorem no_public_decoder_of_difference {W Public World Coins Event : Type}
    (pub : W → Public) (signal : W → World → Coins → Option Event)
    (w u : W) (same : pub w = pub u) (os : World) (coins : Coins)
    (different : signal w os coins ≠ signal u os coins) :
    ¬ ∃ decoder : Public → World → Coins → Option Event,
      ∀ w os coins, signal w os coins = decoder (pub w) os coins := by
  rintro ⟨decoder,law⟩
  exact different (independent_of_public_decoder pub signal decoder law w u same os coins)

#print axioms independent_of_public_decoder
#print axioms public_decoder_of_independent
#print axioms no_public_decoder_of_difference
end R1Z.PV_OptB_Factorization
