import PV_W1_ArgumentEffects
set_option autoImplicit false
noncomputable section
namespace PV_FN_W4_NativeFootprint
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

/-- A native implementation's effects, selected at its actual call entry.
This is a parameter, not a selected identity replacement. -/
abbrev Effects := Entry → OWNER → Address → Option Data

/-- Frame facet of an exact library semantics fact. Unlike Writable this does
not follow references stored in the payload of a scalar Cell. -/
def Confined (C : Carrier OWNER Data) (e : Entry) (w : OWNER)
    (changes : Address → Option Data) (region : Address → Prop) : Prop :=
  ∀ q, ¬ region q →
    (PV_W1_ArgumentEffects.finalStore C e w changes).cells q = e.store.cells q

/-- Join native memory semantics to W1's all-answer return administration.
The final Store stays explicit; no equality of native and reply-only runs is
claimed. This works for faults, failure, divergence and pending as well. -/
theorem deliverFrame {E : Type} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (es : List E) (changes : Address → Option Data)
    (region : Address → Prop) (semantics : Confined C e w changes region)
    (q : Address) (outside : ¬ region q)
    (old : q.activation ≠ e.store.nextActivation)
    (notReturn : q ≠ (⟨e.caller,e.destination,[]⟩ : Address)) :
    (statusStore (deliver C (PV_W1_ArgumentEffects.afterEffects C e w changes)
      (PV_THR2_OwnUniformResourceHandler.lift H
        (.child e.callee e.store.nextActivation e.arguments) w) es).current.status).cells q =
      e.store.cells q := by
  exact ((PV_W1_LeafBoundary.full_reply C
    (PV_W1_ArgumentEffects.afterEffects C e w changes) _ es).2.2.2.2 q old notReturn).trans
      (semantics q outside)

/-- Compose the frame across an explicit native Store and a source suffix.
No proof of reachability or non-aliasing is smuggled into the source frame. -/
theorem join (before native after : Store Data) (region : Address → Prop)
    (nativeFrame : ∀ q, ¬ region q → native.cells q = before.cells q)
    (sourceFrame : ∀ q, ¬ region q → after.cells q = native.cells q) :
    ∀ q, ¬ region q → after.cells q = before.cells q := by
  intro q outside
  exact (sourceFrame q outside).trans (nativeFrame q outside)

#print axioms deliverFrame
#print axioms join
end PV_FN_W4_NativeFootprint
