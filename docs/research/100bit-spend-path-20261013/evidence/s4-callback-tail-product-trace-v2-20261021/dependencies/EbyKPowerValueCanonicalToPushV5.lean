import CurrentPowersConcreteMul
import CurrentWideMulSourceGraph
import AspisR1EbyKPushWideToQ
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKPowerValueCanonicalToPush

abbrev CallbackWide := AspisR1PowersConcreteMul.CallbackWide
abbrev PushWide := AspisR1EbyKPushWideToQ.Wide
abbrev SourceWide := AspisR1PowersConcreteMul.SourceWide

 def callbackToPush (x : CallbackWide) : PushWide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

 def pushToSource (x : PushWide) : SourceWide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def pushCanonical (x : PushWide) : Prop :=
  AspisR1CurrentWideMul.CanonicalWide (pushToSource x)

theorem callbackToPush_current_map (x : CallbackWide) :
    pushToSource (callbackToPush x) = AspisR1PowersConcreteMul.toWide x := by
  rfl

theorem callback_canonical_push (x : CallbackWide)
    (h : AspisR1PowersConcreteMul.Canonical x) : pushCanonical (callbackToPush x) := by
  change AspisR1CurrentWideMul.CanonicalWide (pushToSource (callbackToPush x))
  rw [callbackToPush_current_map]
  exact h

theorem canonical_push_limb_bounds (x : PushWide) (h : pushCanonical x) :
    x.c0.c0.a.val ≤ 2^31-2 ∧ x.c0.c0.b.val ≤ 2^31-2 ∧
    x.c0.c1.a.val ≤ 2^31-2 ∧ x.c0.c1.b.val ≤ 2^31-2 ∧
    x.c1.c0.a.val ≤ 2^31-2 ∧ x.c1.c0.b.val ≤ 2^31-2 ∧
    x.c1.c1.a.val ≤ 2^31-2 ∧ x.c1.c1.b.val ≤ 2^31-2 := by
  change AspisR1CurrentWideMul.CanonicalWide (pushToSource x) at h
  change
    ((x.c0.c0.a.val < 2147483647 ∧ x.c0.c0.b.val < 2147483647) ∧
     (x.c0.c1.a.val < 2147483647 ∧ x.c0.c1.b.val < 2147483647)) ∧
    ((x.c1.c0.a.val < 2147483647 ∧ x.c1.c0.b.val < 2147483647) ∧
     (x.c1.c1.a.val < 2147483647 ∧ x.c1.c1.b.val < 2147483647)) at h
  rcases h with ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩
  omega

theorem powers_callback_total_push_limb_bounds {N : Usize}
    (p x : CallbackWide)
    (hp : AspisR1PowersConcreteMul.Canonical p)
    (hx : AspisR1PowersConcreteMul.Canonical x) (i : Usize) :
    ∃ nextState : AspisR1CurrentPowers.weights.powers.closure N,
      AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
        AspisR1PowersConcreteMul.sourceMul (N := N) (p,x) i = .ok (p,nextState) ∧
      AspisR1PowersConcreteMul.Canonical nextState.1 ∧
      pushCanonical (callbackToPush p) ∧
      (callbackToPush p).c0.c0.a.val ≤ 2^31-2 ∧
      (callbackToPush p).c0.c0.b.val ≤ 2^31-2 ∧
      (callbackToPush p).c0.c1.a.val ≤ 2^31-2 ∧
      (callbackToPush p).c0.c1.b.val ≤ 2^31-2 ∧
      (callbackToPush p).c1.c0.a.val ≤ 2^31-2 ∧
      (callbackToPush p).c1.c0.b.val ≤ 2^31-2 ∧
      (callbackToPush p).c1.c1.a.val ≤ 2^31-2 ∧
      (callbackToPush p).c1.c1.b.val ≤ 2^31-2 := by
  obtain ⟨next, hnext, hcall⟩ :=
    AspisR1PowersConcreteMul.powers_callback_total_canonical p x hp hx i
  have hc := callback_canonical_push p hp
  have hb := canonical_push_limb_bounds (callbackToPush p) hc
  exact ⟨(next,x), hcall, hnext, hc, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1,
    hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2⟩

theorem powers_callback_value_push_limb_bounds {N : Usize}
    (p x value : CallbackWide)
    (next : AspisR1CurrentPowers.weights.powers.closure N)
    (hp : AspisR1PowersConcreteMul.Canonical p)
    (hx : AspisR1PowersConcreteMul.Canonical x) (i : Usize)
    (h : AspisR1CurrentPowers.weights.powers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
      AspisR1PowersConcreteMul.sourceMul (N := N) (p,x) i = .ok (value,next)) :
    pushCanonical (callbackToPush value) ∧
    (callbackToPush value).c0.c0.a.val ≤ 2^31-2 ∧
    (callbackToPush value).c0.c0.b.val ≤ 2^31-2 ∧
    (callbackToPush value).c0.c1.a.val ≤ 2^31-2 ∧
    (callbackToPush value).c0.c1.b.val ≤ 2^31-2 ∧
    (callbackToPush value).c1.c0.a.val ≤ 2^31-2 ∧
    (callbackToPush value).c1.c0.b.val ≤ 2^31-2 ∧
    (callbackToPush value).c1.c1.a.val ≤ 2^31-2 ∧
    (callbackToPush value).c1.c1.b.val ≤ 2^31-2 := by
  obtain ⟨hvalue, _, _⟩ :=
    AspisR1PowersConcreteMul.powers_callback_success_canonical p x value next hp hx i h
  subst value
  have hc := callback_canonical_push p hp
  have hb := canonical_push_limb_bounds (callbackToPush p) hc
  exact ⟨hc, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1,
    hb.2.2.2.2.1, hb.2.2.2.2.2.1, hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2⟩

#print axioms callbackToPush_current_map
#print axioms callback_canonical_push
#print axioms canonical_push_limb_bounds
#print axioms powers_callback_value_push_limb_bounds
#print axioms powers_callback_total_push_limb_bounds
end AspisR1EbyKPowerValueCanonicalToPush
