import Init
set_option autoImplicit false
namespace NEF
structure CM (B : Type) where
  a : B
  b : B
  deriving DecidableEq
/-- Every primitive has its complete state/error/effect meaning in the type M. -/
def invWith {B : Type} {M : Type → Type} [Monad M]
    (mul add : B → B → M B) (neg : B → M B) (inverse : B → M B) (x : CM B) : M (CM B) := do
  let aa ← mul x.a x.a
  let bb ← mul x.b x.b
  let norm ← add aa bb
  let invNorm ← inverse norm
  let a ← mul x.a invNorm
  let nb ← neg x.b
  let b ← mul nb invNorm
  pure ⟨a,b⟩

def invStatic {B : Type} {M : Type → Type} [Monad M]
    (mul add : B → B → M B) (neg baseInv : B → M B) (x : CM B) : M (CM B) := do
  let aa ← mul x.a x.a
  let bb ← mul x.b x.b
  let norm ← add aa bb
  let invNorm ← baseInv norm
  let a ← mul x.a invNorm
  let nb ← neg x.b
  let b ← mul nb invNorm
  pure ⟨a,b⟩
/-- Beta-specialisation; no canonicality, invertibility or arithmetic law needed.
When M is state+error+trace, the equality includes all those observations. -/
theorem inv_with_static {B : Type} {M : Type → Type} [Monad M]
    (mul add : B → B → M B) (neg baseInv : B → M B) (x : CM B) :
    invWith mul add neg baseInv x = invStatic mul add neg baseInv x := rfl

/-- Equality of the selected backend is a named input for any non-direct caller. -/
theorem inv_with_backend_transport {B : Type} {M : Type → Type} [Monad M]
    (mul add : B → B → M B) (neg backend baseInv : B → M B)
    (selected : backend = baseInv) (x : CM B) :
    invWith mul add neg backend x = invStatic mul add neg baseInv x := by
  subst backend
  rfl
#print axioms inv_with_static
#print axioms inv_with_backend_transport
end NEF
