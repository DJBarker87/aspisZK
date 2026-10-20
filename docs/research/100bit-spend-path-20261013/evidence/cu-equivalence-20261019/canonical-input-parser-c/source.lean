import CuSavingsCanonicalInputPowers
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalInputParser
open Aeneas Aeneas.Std Result AspisR1CanonicalInputs
open CuSavingsCanonicalInputPowers
abbrev Words := Array U32 8#usize

def word (xs : Words) (i : Fin 8) : U32 :=
  xs.val[i.val]'(by simpa only [xs.property,show (8#usize).val=8 by scalar_tac] using i.isLt)

theorem array_read (xs : Words) (i : Usize) (hi : i.val<8) :
    Array.index_usize xs i=.ok (word xs ⟨i.val,hi⟩) := by
  have hb : i.val<xs.val.length := by simpa only [xs.property,show (8#usize).val=8 by scalar_tac] using hi
  unfold Array.index_usize word
  simp only [Array.getElem?_Usize_eq,List.getElem?_eq_getElem hb]

theorem from_limbs_success (xs : Words) (x : E)
    (h : field.wide_exact.WideExact.from_limbs xs=.ok (some x)) : Canonical x := by
  simp only [field.wide_exact.WideExact.from_limbs,
    array_read xs 0#usize (by decide),
    array_read xs 1#usize (by decide),
    array_read xs 2#usize (by decide),
    array_read xs 3#usize (by decide),
    array_read xs 4#usize (by decide),
    array_read xs 5#usize (by decide),
    array_read xs 6#usize (by decide),
    array_read xs 7#usize (by decide),bind_tc_ok] at h
  split at h
  · cases h
  · rename_i hn0
    split at h
    · cases h
    · rename_i hn1
      split at h
      · cases h
      · rename_i hn2
        split at h
        · cases h
        · rename_i hn3
          split at h
          · cases h
          · rename_i hn4
            split at h
            · cases h
            · rename_i hn5
              split at h
              · cases h
              · rename_i hn6
                split at h
                · cases h
                · rename_i hn7
                  have he := Option.some.inj (Result.ok.inj h)
                  cases he
                  have hv0 : (word xs 0).val<2147483647 := by
                    simp only [field.P,UScalar.le_equiv] at hn0
                    change ¬2147483647≤(word xs 0).val at hn0
                    exact Nat.lt_of_not_ge hn0
                  have hv1 : (word xs 1).val<2147483647 := by
                    simp only [field.P,UScalar.le_equiv] at hn1
                    change ¬2147483647≤(word xs 1).val at hn1
                    exact Nat.lt_of_not_ge hn1
                  have hv2 : (word xs 2).val<2147483647 := by
                    simp only [field.P,UScalar.le_equiv] at hn2
                    change ¬2147483647≤(word xs 2).val at hn2
                    exact Nat.lt_of_not_ge hn2
                  have hv3 : (word xs 3).val<2147483647 := by
                    simp only [field.P,UScalar.le_equiv] at hn3
                    change ¬2147483647≤(word xs 3).val at hn3
                    exact Nat.lt_of_not_ge hn3
                  have hv4 : (word xs 4).val<2147483647 := by
                    simp only [field.P,UScalar.le_equiv] at hn4
                    change ¬2147483647≤(word xs 4).val at hn4
                    exact Nat.lt_of_not_ge hn4
                  have hv5 : (word xs 5).val<2147483647 := by
                    simp only [field.P,UScalar.le_equiv] at hn5
                    change ¬2147483647≤(word xs 5).val at hn5
                    exact Nat.lt_of_not_ge hn5
                  have hv6 : (word xs 6).val<2147483647 := by
                    simp only [field.P,UScalar.le_equiv] at hn6
                    change ¬2147483647≤(word xs 6).val at hn6
                    exact Nat.lt_of_not_ge hn6
                  have hv7 : (word xs 7).val<2147483647 := by
                    simp only [field.P,UScalar.le_equiv] at hn7
                    change ¬2147483647≤(word xs 7).val at hn7
                    exact Nat.lt_of_not_ge hn7
                  change (((word xs 0).val<2147483647 ∧ (word xs 1).val<2147483647) ∧
                    ((word xs 2).val<2147483647 ∧ (word xs 3).val<2147483647)) ∧
                  (((word xs 4).val<2147483647 ∧ (word xs 5).val<2147483647) ∧
                    ((word xs 6).val<2147483647 ∧ (word xs 7).val<2147483647))
                  exact ⟨⟨⟨hv0,hv1⟩,⟨hv2,hv3⟩⟩,⟨⟨hv4,hv5⟩,⟨hv6,hv7⟩⟩⟩

#print axioms array_read
#print axioms from_limbs_success
end AspisR1.CuSavingsCanonicalInputParser
