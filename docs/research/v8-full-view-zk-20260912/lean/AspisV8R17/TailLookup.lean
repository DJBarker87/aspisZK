import AspisV8R17.SourceMinor

/-! Symbolic source-tail membership; concrete generators check only drop identities. -/
set_option autoImplicit false
namespace AspisV8R17.SourceMinor

theorem tail_lookup_mem (xs ys : List ℕ) (offset n : ℕ)
    (hd : xs.drop offset = ys) (hl : xs.length = offset+n) (i : Fin n) :
    xs.getD (offset+i.val) 0 ∈ ys := by
  have hi : offset+i.val < xs.length := by rw [hl]; omega
  have ht : i.val < (xs.drop offset).length := by rw [List.length_drop, hl]; omega
  rw [← hd, List.getD_eq_getElem _ _ hi]
  simpa only [List.getElem_drop] using (List.getElem_mem (l := xs.drop offset) (h := ht))

#print axioms tail_lookup_mem
end AspisV8R17.SourceMinor
