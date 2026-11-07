import NGC_DigestBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_DigestBridge
/-- The SAME runtime hash slot and complete ordered descriptor slice as the
CLOSED NGC packet; no SHA value law is supplied here. -/
def poolDigest (hashv : Slice (Slice U8) → Array U8 32#usize) (parts : Slice (Slice U8)) :=
 (AspisR1.NGC_DigestBridge.backend hashv).digest () parts

theorem row_368 (hashv : Slice (Slice U8) → Array U8 32#usize) (parts : Slice (Slice U8))
 (_count : parts.val.length ≤ 9) (_lengths : ∀ p ∈ parts.val, p.val.length ≤ 57607) :
 poolDigest hashv parts = ok (hashv parts) :=
 AspisR1.NGC_DigestBridge.forwarding hashv parts
#print axioms row_368
end PCG_DigestBridge
