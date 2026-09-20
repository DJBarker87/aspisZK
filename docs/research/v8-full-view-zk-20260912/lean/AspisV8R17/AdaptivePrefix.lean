import AspisV8H1C2.FiniteTransport

/-! Selecting a correction using the realized prefix needs an additional
two-sided source invariant. This file does not establish that invariant
for commitments, oracle tapes, or V8. -/
set_option autoImplicit false
namespace AspisV8R17
variable {X P V : Type*}

def adaptivePrefixEquiv (left right : X → P) (e : P → X ≃ X)
    (forward : ∀ p x, left x = p → right (e p x) = p)
    (backward : ∀ p y, right y = p → left ((e p).symm y) = p) : X ≃ X where
  toFun x := e (left x) x
  invFun y := (e (right y)).symm y
  left_inv x := by
    change (e (right (e (left x) x))).symm (e (left x) x) = x
    rw [forward (left x) x rfl]
    exact (e (left x)).symm_apply_apply x
  right_inv y := by
    change e (left ((e (right y)).symm y)) ((e (right y)).symm y) = y
    rw [backward (right y) y rfl]
    exact (e (right y)).apply_symm_apply y

theorem adaptive_prefix_same_uniform_law [Fintype X] [Nonempty X]
    (left right : X → P) (e : P → X ≃ X)
    (forward : ∀ p x, left x = p → right (e p x) = p)
    (backward : ∀ p y, right y = p → left ((e p).symm y) = p)
    (obsL obsR : X → V)
    (commutes : ∀ p x, left x = p → obsR (e p x) = obsL x) :
    AspisV8H1C2.SameUniformLaw obsL obsR := by
  apply AspisV8H1C2.sameUniformLaw_of_equiv obsL obsR
    (adaptivePrefixEquiv left right e forward backward)
  intro x
  exact commutes (left x) x rfl

/-- Every fixed-prefix map is bijective, but choosing the prefix from the
input can collapse both inputs. This is a warning, not a V8 attack. -/
def prefixFlip (p x : Bool) : Bool := if p then !x else x

theorem prefixFlip_bijective (p : Bool) : Function.Bijective (prefixFlip p) := by
  cases p <;> decide

theorem selectedPrefixFlip_constant (x : Bool) : prefixFlip x x = false := by
  cases x <;> rfl

theorem selectedPrefixFlip_not_injective :
    ¬ Function.Injective (fun x : Bool => prefixFlip x x) := by
  intro h
  have impossible : true = false := h (by rfl)
  cases impossible

#print axioms adaptivePrefixEquiv
#print axioms adaptive_prefix_same_uniform_law
#print axioms prefixFlip_bijective
#print axioms selectedPrefixFlip_constant
#print axioms selectedPrefixFlip_not_injective
end AspisV8R17
