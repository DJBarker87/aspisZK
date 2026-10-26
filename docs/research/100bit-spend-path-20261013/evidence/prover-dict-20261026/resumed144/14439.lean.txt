import Aeneas
set_option autoImplicit false
namespace R1Z.PDict_MessageExtensional
/-- Proof principle used by the native one-arbitrary-byte Debug contract.
It requires every valid position and equal lengths, not a sampled-byte law. -/
theorem message_eq (actual expected : List UInt8)
    (length_eq : actual.length = expected.length)
    (byte_eq : ∀ i (ha : i < actual.length) (he : i < expected.length),
      actual[i] = expected[i]) : actual = expected := by
  exact List.ext_getElem length_eq byte_eq

/-- Lifts that complete message equality to the one-call sink trace while
retaining its arbitrary state. No native vtable/carrier association is inferred. -/
theorem one_call_trace {S : Type} (actual expected : List UInt8) (state : S)
    (length_eq : actual.length = expected.length)
    (byte_eq : ∀ i (ha : i < actual.length) (he : i < expected.length),
      actual[i] = expected[i]) : [(actual,state)] = [(expected,state)] := by
  rw [message_eq actual expected length_eq byte_eq]

#print axioms message_eq
#print axioms one_call_trace
end R1Z.PDict_MessageExtensional
