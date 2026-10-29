import R1Z.PV_OWNO_SampleEight
set_option autoImplicit false
namespace R1Z.PV_OWNP_SampleCarrier
open Aeneas Aeneas.Std PV_OWNL_SampleWord
attribute [local irreducible] u32 u64 dividend quotient rem64 truncate

/-- Bounded remainder and an arbitrary raw input word fit the source U64
shift/OR dividend without modular wraparound. -/
theorem dividend_exact (r : U64) (w : U32) (hr : r.val < 2147483647) :
 (dividend r w).val = r.val * 4294967296 + w.val := by
 have hw := w.hBounds
 unfold dividend u64
 change (r.val * 4294967296 + w.val) % 18446744073709551616 = _
 apply Nat.mod_eq_of_lt
 omega

theorem quotient_exact (r : U64) (w : U32) (hr : r.val < 2147483647) :
 (quotient (dividend r w)).val = (r.val * 4294967296 + w.val) / 2147483647 := by
 have hw := w.hBounds
 have hd := dividend_exact r w hr
 unfold quotient u32
 change ((dividend r w).val / 2147483647) % 4294967296 = _
 rw [hd]
 apply Nat.mod_eq_of_lt
 omega

theorem remainder_exact (n : U64) : (rem64 n).val = n.val % 2147483647 := by
 unfold rem64 u64
 change (n.val % 2147483647) % 18446744073709551616 = _
 apply Nat.mod_eq_of_lt
 have h := Nat.mod_lt n.val (show 0 < 2147483647 by omega)
 omega

theorem truncate_exact (n : U64) (hn : n.val < 2147483647) :
 (truncate n).val = n.val := by
 unfold truncate u32
 change n.val % 4294967296 = n.val
 exact Nat.mod_eq_of_lt (by omega)

/-- No quotient limb is lost or reordered by the complete pass. -/
theorem step_words (s : PV_OWNO_SampleEight.State) (w : U32) :
 (PV_OWNO_SampleEight.step dividend s w).words =
  s.words ++ [quotient (dividend s.remainder w)] := rfl

#print axioms dividend_exact
#print axioms quotient_exact
#print axioms remainder_exact
#print axioms truncate_exact
#print axioms step_words
end R1Z.PV_OWNP_SampleCarrier
