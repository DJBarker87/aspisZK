import NJJ_Common
set_option autoImplicit false
namespace NJJ_DomainAudit
open Aeneas Aeneas.Std
/-- The root's Slice input type alone gives no1880 public-byte bound. Any
valid length is representable; an additional bound must come from an actual
caller theorem, not the address or the name of the public callback. -/
theorem public_lengths (n : Nat) (fits : n≤Usize.max) :
 ∃ pubBytes : Slice U8,pubBytes.val.length=n := by
 refine ⟨⟨List.replicate n 0#u8,?_⟩,?_⟩
 · simpa only [List.length_replicate] using fits
 · exact List.length_replicate
#print axioms public_lengths
end NJJ_DomainAudit
