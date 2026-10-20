import CuSavingsCanonicalInputPowers
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalInputParser
open Aeneas Aeneas.Std Result AspisR1CanonicalInputs
open CuSavingsCanonicalInputPowers
abbrev Words := Array U32 8#usize

def word (xs : Words) (i : Fin 8) : U32 :=
  xs.val[i.val]'(by simpa only [xs.property] using i.isLt)

theorem array_read (xs : Words) (i : Usize) (hi : i.val<8) :
    Array.index_usize xs i=.ok (word xs ⟨i.val,hi⟩) := by
  have hb : i.val<xs.val.length := by simpa only [xs.property] using hi
  unfold Array.index_usize
  change (match xs.val[i.val]? with
    | none => .fail Error.arrayOutOfBounds
    | some x => .ok x)=.ok (xs.val[i.val]'hb)
  rw [List.getElem?_eq_getElem hb]

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
                    simp only [field.P] at hn0
                    scalar_tac
                  have hv1 : (word xs 1).val<2147483647 := by
                    simp only [field.P] at hn1
                    scalar_tac
                  have hv2 : (word xs 2).val<2147483647 := by
                    simp only [field.P] at hn2
                    scalar_tac
                  have hv3 : (word xs 3).val<2147483647 := by
                    simp only [field.P] at hn3
                    scalar_tac
                  have hv4 : (word xs 4).val<2147483647 := by
                    simp only [field.P] at hn4
                    scalar_tac
                  have hv5 : (word xs 5).val<2147483647 := by
                    simp only [field.P] at hn5
                    scalar_tac
                  have hv6 : (word xs 6).val<2147483647 := by
                    simp only [field.P] at hn6
                    scalar_tac
                  have hv7 : (word xs 7).val<2147483647 := by
                    simp only [field.P] at hn7
                    scalar_tac
                  change (((word xs 0).val<2147483647 ∧ (word xs 1).val<2147483647) ∧
                    ((word xs 2).val<2147483647 ∧ (word xs 3).val<2147483647)) ∧
                  (((word xs 4).val<2147483647 ∧ (word xs 5).val<2147483647) ∧
                    ((word xs 6).val<2147483647 ∧ (word xs 7).val<2147483647))
                  exact ⟨⟨⟨hv0,hv1⟩,⟨hv2,hv3⟩⟩,⟨⟨hv4,hv5⟩,⟨hv6,hv7⟩⟩⟩

#print axioms array_read
#print axioms from_limbs_success
end AspisR1.CuSavingsCanonicalInputParser
