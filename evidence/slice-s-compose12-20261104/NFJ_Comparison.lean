import NFH_ComparisonDomain
set_option autoImplicit false
namespace NFJ_Comparison
open Aeneas Aeneas.Std

/-- RuntimeMemcmp (ac), ADDED trust, pending owner confirmation.
Only the zero law for the SAME two retained 688-byte ranges is consumed here.
Normal return, result-slot identity and the observable frame are the separate
native forwarding certificate and the explicitly named runtime row. -/
abbrev RuntimeMemcmp := NFH_ComparisonDomain.At688Law

def header (bytes : List U8) : List U8 := bytes.take 688

theorem header_length (bytes : List U8) (acceptedLength : bytes.length = 58295) :
    (header bytes).length = 688 := by
  simp only [header,List.length_take,acceptedLength]
  rfl

theorem same_buffer_lengths (bytes : List U8) (acceptedLength : bytes.length = 58295)
    (encoded : Array U8 688#usize) :
    encoded.val.length = 688 ∧ (header bytes).length = 688 :=
  ⟨encoded.property,header_length bytes acceptedLength⟩

/-- This applies the 688-only law AFTER establishing both SAME buffer lengths;
it never asserts a runtime law for another length. -/
theorem nativeEqualityBridge (reply : List U8 → List U8 → Int)
    (runtimeMemcmp : RuntimeMemcmp reply) (bytes : List U8)
    (acceptedLength : bytes.length = 58295) (encoded : Array U8 688#usize) :
    decide (reply encoded.val (header bytes) = 0) =
      NFH_ComparisonDomain.complete688 reply encoded.val (header bytes) := by
  exact (NFH_ComparisonDomain.complete688_on_domain reply encoded.val (header bytes)
    (same_buffer_lengths bytes acceptedLength encoded).1
    (same_buffer_lengths bytes acceptedLength encoded).2).symm

/-- Equal and unequal branches use exactly the slot's zero observation. -/
theorem slot_zero_iff (reply : List U8 → List U8 → Int)
    (runtimeMemcmp : RuntimeMemcmp reply) (bytes : List U8)
    (acceptedLength : bytes.length = 58295) (encoded : Array U8 688#usize) :
    reply encoded.val (header bytes) = 0 ↔ encoded.val = header bytes := by
  exact runtimeMemcmp encoded.val (header bytes) encoded.property
    (header_length bytes acceptedLength)

/-- The mathematical completion supplies the old universal MODEL interface;
only nativeEqualityBridge above licenses native use on the reached domain. -/
theorem completion (reply : List U8 → List U8 → Int)
    (runtimeMemcmp : RuntimeMemcmp reply) :
    NFD_ScanConditional.NativeEqualityAssociation
      (NFH_ComparisonDomain.complete688 reply) :=
  NFH_ComparisonDomain.complete688_association reply runtimeMemcmp

#print axioms header_length
#print axioms same_buffer_lengths
#print axioms nativeEqualityBridge
#print axioms slot_zero_iff
#print axioms completion
end NFJ_Comparison
