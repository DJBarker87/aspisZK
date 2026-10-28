import R1Z.PV_RDEA_CapacityEndpoint
namespace R1Z.PV_RDEA_PrefixWords
abbrev Word := List (Nat × Nat × Nat)
def Prefix (observed planned : Word) : Prop := ∃ suffix,observed++suffix=planned

theorem refl (word : Word) : Prefix word word := ⟨[],List.append_nil _⟩
theorem nil (word : Word) : Prefix [] word := ⟨word,rfl⟩
theorem right (a b c : Word) (h : Prefix a b) : Prefix a (b++c) := by
  obtain ⟨suffix,hs⟩ := h
  exact ⟨suffix++c,by rw [← List.append_assoc,hs]⟩
theorem left (before a b : Word) (h : Prefix a b) : Prefix (before++a) (before++b) := by
  obtain ⟨suffix,hs⟩ := h
  exact ⟨suffix,by rw [List.append_assoc,hs]⟩
theorem trans (a b c : Word) (hab : Prefix a b) (hbc : Prefix b c) : Prefix a c := by
  obtain ⟨suffix,hs⟩ := hab
  obtain ⟨tail,ht⟩ := hbc
  exact ⟨suffix++tail,by rw [← List.append_assoc,hs,ht]⟩

/-- First failed allocation may terminate the execution. This keeps the
failure event visible while describing its public request-prefix shape. -/
def cloneWord (n : Nat) : Word := if n=0 then [] else [(0,n,1)]

theorem constructor_prefix (n : Nat) :
    Prefix (PV_RDEA_CapacityEndpoint.requestSizes n) (cloneWord n) := by
  unfold PV_RDEA_CapacityEndpoint.requestSizes
  split
  · exact nil _
  · split
    · exact nil _
    · split <;> rename_i hz
      · rw [cloneWord,hz,if_pos rfl]
        exact refl _
      · rw [cloneWord,if_neg hz]
        exact refl _

#print axioms refl
#print axioms nil
#print axioms right
#print axioms left
#print axioms trans
#print axioms constructor_prefix
end R1Z.PV_RDEA_PrefixWords
