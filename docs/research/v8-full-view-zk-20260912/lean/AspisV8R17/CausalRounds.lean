import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Equiv.Defs

/-! Any finite number of causal additive cuts. This is an exact bijection
of ideal coin coordinates, not a claim about commitments or the source oracle. -/
set_option autoImplicit false
namespace AspisV8R17
universe u
variable {A Z F : Type*} [AddCommGroup A] [AddCommGroup F]

def RoundCoins (A : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => A × RoundCoins A n

/-- The state can contain prior sent messages, their oracle challenges, and
fixed non-G context. It must not inspect future coins: this signature is
the causal premise that a source refinement still has to discharge. -/
def causalRounds : (n : ℕ) → (Z → A) → (Z → A → Z) → Z →
    RoundCoins A n ≃ RoundCoins A n
  | 0, _, _, _ => Equiv.refl _
  | n+1, offset, next, z => {
      toFun := fun x =>
        let y := x.1 + offset z
        (y, causalRounds n offset next (next z y) x.2)
      invFun := fun y =>
        (y.1 - offset z, (causalRounds n offset next (next z y.1)).symm y.2)
      left_inv := by intro x; rcases x with ⟨a,b⟩; simp
      right_inv := by intro y; rcases y with ⟨a,b⟩; simp }

/-- In particular the initial scalar is sent before the state (and eta)
for the first polynomial is constructed from that scalar. -/
def initialThenRounds (n : ℕ) (initialOffset : F) (state : F → Z)
    (offset : Z → A) (next : Z → A → Z) :
    (F × RoundCoins A n) ≃ (F × RoundCoins A n) where
  toFun x := let y := x.1 + initialOffset
    (y, causalRounds n offset next (state y) x.2)
  invFun y := (y.1 - initialOffset,
    (causalRounds n offset next (state y.1)).symm y.2)
  left_inv x := by rcases x with ⟨a,b⟩; simp
  right_inv y := by rcases y with ⟨a,b⟩; simp

/-- Retain context rather than resampling it after observing the cuts. -/
def contextFiber {C V : Type*} (e : C → V ≃ V) (view : V) :
    C ≃ {x : C × V // e x.1 x.2 = view} where
  toFun c := ⟨(c, (e c).symm view), by simp⟩
  invFun x := x.1.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h := congrArg (e x.1.1).symm x.2
      simpa using h.symm

#print axioms causalRounds
#print axioms initialThenRounds
#print axioms contextFiber
end AspisV8R17
