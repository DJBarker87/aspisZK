import NFV_Envelope
import NED_WindowExtensionality
set_option autoImplicit false
namespace NFV_RequestWindows
open Aeneas Aeneas.Std Result
abbrev Bytes := NFV_Envelope.Bytes

def point (a b : Bytes) (i : Fin (320#usize).val) : Prop :=
  a.val[i.val]'(by rw [a.property]; exact i.isLt) =
  b.val[i.val]'(by rw [b.property]; exact i.isLt)

/-- Five arbitrary-index native observations cover the entire request. This
lemma composes observations that must each be supplied by a native certificate. -/
theorem complete (actual expected : Bytes)
    (header : ∀ i, i.val < 8 → point actual expected i)
    (profile : ∀ i, 8 ≤ i.val → i.val < 40 → point actual expected i)
    (release : ∀ i, 40 ≤ i.val → i.val < 72 → point actual expected i)
    (program : ∀ i, 72 ≤ i.val → i.val < 104 → point actual expected i)
    (payment : ∀ i, 104 ≤ i.val → point actual expected i) : actual = expected := by
  apply NED_WindowExtensionality.array_ext
  intro i
  by_cases h0 : i.val < 8
  · exact header i h0
  by_cases h1 : i.val < 40
  · exact profile i (by omega) h1
  by_cases h2 : i.val < 72
  · exact release i (by omega) h2
  by_cases h3 : i.val < 104
  · exact program i (by omega) h3
  exact payment i (by omega)
#print axioms complete

/-- The emitted envelope can be replaced only AFTER all five native windows
have supplied their observations on the SAME returned array. -/
theorem envelope (actual : Bytes) (profile release program : NFV_Envelope.Bytes32)
    (kind : U8) (payment : NFV_Envelope.Payment)
    (header : ∀ i, i.val < 8 → point actual (NFV_Envelope.pure profile release program kind payment) i)
    (hp : ∀ i, 8 ≤ i.val → i.val < 40 → point actual (NFV_Envelope.pure profile release program kind payment) i)
    (hr : ∀ i, 40 ≤ i.val → i.val < 72 → point actual (NFV_Envelope.pure profile release program kind payment) i)
    (hb : ∀ i, 72 ≤ i.val → i.val < 104 → point actual (NFV_Envelope.pure profile release program kind payment) i)
    (ht : ∀ i, 104 ≤ i.val → point actual (NFV_Envelope.pure profile release program kind payment) i) :
    AspisR20Request.pool_v1.pair_forest_terminal.asq8_reference_envelope
      profile release program kind payment = ok actual := by
  rw [NFV_Envelope.emitted,complete actual _ header hp hr hb ht]
#print axioms envelope
end NFV_RequestWindows
