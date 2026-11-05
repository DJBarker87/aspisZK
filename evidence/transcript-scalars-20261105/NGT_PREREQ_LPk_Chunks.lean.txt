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
open AspisR1.SamplerMachineBounds
/-- Composition of the four native gates, after quotient/remainder bounds
and Rust word/cast semantics have been transported to natural values. -/
theorem native_relation {rem limb q r : Nat}
    (hrem : rem < P) (hlimb : limb < B) (hq : q < B) (hr : r < P)
    (h0 : (q*P+r) % 65536 = (rem*B+limb) % 65536)
    (h1 : (q*P+r) / 65536 % 65536 = (rem*B+limb) / 65536 % 65536)
    (h2 : (q*P+r) / 4294967296 % 65536 = (rem*B+limb) / 4294967296 % 65536)
    (h3 : (q*P+r) / 281474976710656 % 65536 =
      (rem*B+limb) / 281474976710656 % 65536) :
    LPk_Step.Relation rem limb q r := by
  refine ⟨join (LPk_Modular.no_wrap hq hr) ?_ h0 h1 h2 h3,hr⟩
  exact (dividend_lt_two63 hrem hlimb).trans (by norm_num)
#print axioms join
#print axioms native_relation
end LPk_Chunks
