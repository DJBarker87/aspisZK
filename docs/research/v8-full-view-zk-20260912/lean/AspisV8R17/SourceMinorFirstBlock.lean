import AspisV8R17.SourceMinor
import AspisV8R17.SourceBlockEntries00
import AspisV8R17.SourceBlockSupport00

/-! First concrete ordered block: bind the source matrix, not a synthetic
triangular matrix. The remaining tail determinant is a separate obligation. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor

theorem first_tail_membership : ∀ i : Fin 213,
    orderedRows.getD (i.val+1) 0 ∈ SourceBlockSupport.column5_later := by
  intro i
  have he : orderedRows = 126 :: SourceBlockSupport.column5_later := by decide
  have hl : SourceBlockSupport.column5_later.length = 213 := by decide
  rw [he]
  change SourceBlockSupport.column5_later.getD i.val 0 ∈ SourceBlockSupport.column5_later
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact i.isLt)]
  exact List.getElem_mem _

theorem first_lower_zero {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 213) :
    orderedMinor half alpha a b c ⟨i.val+1, by omega⟩ 0 = 0 := by
  rw [orderedMinor_entry]
  change sourceChord half (fun j => unitVector 123 j-alpha^3*unitVector 120 j)
    a b c (orderedRows.getD (i.val+1) 0) = 0
  exact SourceBlockSupport.column5_zero half (alpha^3) a b c _ (first_tail_membership i)

theorem first_diagonal :
    orderedMinor (1073741824 : ZMod 2147483647) 2 13 11 (-7) 0 0 = 1073741827 := by
  rw [orderedMinor_entry]
  change entry (1073741824 : ZMod 2147483647) 2 13 11 (-7) 126 26 = 1073741827
  unfold entry
  simp only [show 4*(22+26/3) = 120 from rfl,
    show 1+26%3 = 3 from rfl, show 120+3 = 123 from rfl]
  rw [show (2 : ZMod 2147483647)^3 = 8 from by decide]
  exact SourceBlocks.block3_entry0_0

#print axioms first_tail_membership
#print axioms first_lower_zero
#print axioms first_diagonal
end AspisV8R17.SourceMinor
