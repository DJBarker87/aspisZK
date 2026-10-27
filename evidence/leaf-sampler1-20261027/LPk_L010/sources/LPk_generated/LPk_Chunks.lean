import LPk_Modular
set_option autoImplicit false
namespace LPk_Chunks
/-- Four disjoint native 16-bit projections suffice for equality of u64
values; no single projection is promoted to a full relation. -/
theorem join {a b : Nat} (ha : a < 2^64) (hb : b < 2^64)
    (h0 : a % 65536 = b % 65536)
    (h1 : a / 65536 % 65536 = b / 65536 % 65536)
    (h2 : a / 4294967296 % 65536 = b / 4294967296 % 65536)
    (h3 : a / 281474976710656 % 65536 = b / 281474976710656 % 65536) :
    a = b := by
  omega
#print axioms join
end LPk_Chunks
