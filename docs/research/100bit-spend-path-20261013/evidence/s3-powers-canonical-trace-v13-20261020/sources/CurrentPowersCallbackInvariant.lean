import CurrentPowersExactProduct
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PowersExactProduct
open AspisR1PowersConcreteMul

/-- This is an invariant of the unchanged emitted callback, not a claim that
Rust from_fn has yet been linked to its traversal model. -/
theorem powers_callback_success_power_invariant {N : Usize} (p x value : CallbackWide)
    (next : AspisR1CurrentPowers.weights.powers.closure N)
    (hp : Canonical p) (hx : Canonical x) (i : Usize) (n : Nat)
    (hpower : decode p = decode x ^ n)
    (h : AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
      sourceMul (N := N) (p,x) i = .ok (value,next)) :
    Canonical value ∧ decode value = decode x ^ n ∧ next.2 = x ∧
      Canonical next.1 ∧ decode next.1 = decode x ^ (n+1) := by
  obtain ⟨hv,hxnext,hc,he⟩ := powers_callback_success_exact p x value next hp hx i h
  refine ⟨?_,?_,hxnext,hc,?_⟩
  · simpa only [hv] using hp
  · simpa only [hv] using hpower
  · rw [he,hpower,pow_succ]

#print axioms powers_callback_success_power_invariant
end AspisR1PowersExactProduct
