import S1PowersCallbackChainV1
set_option autoImplicit false
namespace AspisS1PowersCallbackChain
open Aeneas Aeneas.Std Result
open AspisR1PowersConcreteMul AspisR1PowersExactProduct

private theorem word_eq (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647)
    (same : (a.val : ZMod 2147483647)=(b.val : ZMod 2147483647)) : a=b := by
  apply UScalar.eq_of_val_eq
  have vals := congrArg ZMod.val same
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using vals

/-- Equality of decoded canonical values implies equality of ALL eight raw
u32 words. No quotient/reduced carrier is substituted for the callback value. -/
theorem canonical_injective (x y : E) (hx : Canonical x) (hy : Canonical y)
    (same : decode x=decode y) : x=y := by
  rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rcases y with ⟨⟨⟨a',b'⟩,⟨c',d'⟩⟩,⟨⟨e',f'⟩,⟨g',h'⟩⟩⟩
  change ((a.val<2147483647 ∧ b.val<2147483647) ∧
    (c.val<2147483647 ∧ d.val<2147483647)) ∧
    ((e.val<2147483647 ∧ f.val<2147483647) ∧
    (g.val<2147483647 ∧ h.val<2147483647)) at hx
  change ((a'.val<2147483647 ∧ b'.val<2147483647) ∧
    (c'.val<2147483647 ∧ d'.val<2147483647)) ∧
    ((e'.val<2147483647 ∧ f'.val<2147483647) ∧
    (g'.val<2147483647 ∧ h'.val<2147483647)) at hy
  have aEq : a=a' := word_eq a a' hx.1.1.1 hy.1.1.1
    (congrArg (fun value => value.re.re.re) same)
  have bEq : b=b' := word_eq b b' hx.1.1.2 hy.1.1.2
    (congrArg (fun value => value.re.re.im) same)
  have cEq : c=c' := word_eq c c' hx.1.2.1 hy.1.2.1
    (congrArg (fun value => value.re.im.re) same)
  have dEq : d=d' := word_eq d d' hx.1.2.2 hy.1.2.2
    (congrArg (fun value => value.re.im.im) same)
  have eEq : e=e' := word_eq e e' hx.2.1.1 hy.2.1.1
    (congrArg (fun value => value.im.re.re) same)
  have fEq : f=f' := word_eq f f' hx.2.1.2 hy.2.1.2
    (congrArg (fun value => value.im.re.im) same)
  have gEq : g=g' := word_eq g g' hx.2.2.1 hy.2.2.1
    (congrArg (fun value => value.im.im.re) same)
  have hEq : h=h' := word_eq h h' hx.2.2.2 hy.2.2.2
    (congrArg (fun value => value.im.im.im) same)
  cases aEq;cases bEq;cases cEq;cases dEq
  cases eEq;cases fEq;cases gEq;cases hEq
  rfl

#print axioms canonical_injective
end AspisS1PowersCallbackChain
