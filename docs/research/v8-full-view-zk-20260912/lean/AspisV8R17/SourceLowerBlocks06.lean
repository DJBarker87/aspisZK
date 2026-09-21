import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport06

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column125_tail : orderedRows.drop 49 = SourceBlockSupport.column125_later := by decide
theorem column125_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 165) :
    orderedMinor half alpha a b c ⟨49+i.val, by omega⟩ 48 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (49+i.val) 0) 471 = 0
  unfold entry
  simp only [show 4*(22+471/3) = 716 from rfl,
    show 1+471%3 = 1 from rfl, show 716+1 = 717 from rfl]
  exact SourceBlockSupport.column125_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 49 165 column125_tail (by decide) i)
#print axioms column125_tail
#print axioms column125_lower

theorem column129_tail : orderedRows.drop 51 = SourceBlockSupport.column129_later := by decide
theorem column129_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 163) :
    orderedMinor half alpha a b c ⟨51+i.val, by omega⟩ 49 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (51+i.val) 0) 492 = 0
  unfold entry
  simp only [show 4*(22+492/3) = 744 from rfl,
    show 1+492%3 = 1 from rfl, show 744+1 = 745 from rfl]
  exact SourceBlockSupport.column129_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 51 163 column129_tail (by decide) i)
#print axioms column129_tail
#print axioms column129_lower

theorem column130_tail : orderedRows.drop 51 = SourceBlockSupport.column130_later := by decide
theorem column130_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 163) :
    orderedMinor half alpha a b c ⟨51+i.val, by omega⟩ 50 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (51+i.val) 0) 493 = 0
  unfold entry
  simp only [show 4*(22+493/3) = 744 from rfl,
    show 1+493%3 = 2 from rfl, show 744+2 = 746 from rfl]
  exact SourceBlockSupport.column130_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 51 163 column130_tail (by decide) i)
#print axioms column130_tail
#print axioms column130_lower

theorem column128_tail : orderedRows.drop 52 = SourceBlockSupport.column128_later := by decide
theorem column128_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 162) :
    orderedMinor half alpha a b c ⟨52+i.val, by omega⟩ 51 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (52+i.val) 0) 483 = 0
  unfold entry
  simp only [show 4*(22+483/3) = 732 from rfl,
    show 1+483%3 = 1 from rfl, show 732+1 = 733 from rfl]
  exact SourceBlockSupport.column128_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 52 162 column128_tail (by decide) i)
#print axioms column128_tail
#print axioms column128_lower

theorem column132_tail : orderedRows.drop 54 = SourceBlockSupport.column132_later := by decide
theorem column132_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 160) :
    orderedMinor half alpha a b c ⟨54+i.val, by omega⟩ 52 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (54+i.val) 0) 504 = 0
  unfold entry
  simp only [show 4*(22+504/3) = 760 from rfl,
    show 1+504%3 = 1 from rfl, show 760+1 = 761 from rfl]
  exact SourceBlockSupport.column132_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 54 160 column132_tail (by decide) i)
#print axioms column132_tail
#print axioms column132_lower

theorem column133_tail : orderedRows.drop 54 = SourceBlockSupport.column133_later := by decide
theorem column133_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 160) :
    orderedMinor half alpha a b c ⟨54+i.val, by omega⟩ 53 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (54+i.val) 0) 505 = 0
  unfold entry
  simp only [show 4*(22+505/3) = 760 from rfl,
    show 1+505%3 = 2 from rfl, show 760+2 = 762 from rfl]
  exact SourceBlockSupport.column133_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 54 160 column133_tail (by decide) i)
#print axioms column133_tail
#print axioms column133_lower

theorem column131_tail : orderedRows.drop 55 = SourceBlockSupport.column131_later := by decide
theorem column131_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 159) :
    orderedMinor half alpha a b c ⟨55+i.val, by omega⟩ 54 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (55+i.val) 0) 495 = 0
  unfold entry
  simp only [show 4*(22+495/3) = 748 from rfl,
    show 1+495%3 = 1 from rfl, show 748+1 = 749 from rfl]
  exact SourceBlockSupport.column131_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 55 159 column131_tail (by decide) i)
#print axioms column131_tail
#print axioms column131_lower

theorem column135_tail : orderedRows.drop 57 = SourceBlockSupport.column135_later := by decide
theorem column135_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 157) :
    orderedMinor half alpha a b c ⟨57+i.val, by omega⟩ 55 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (57+i.val) 0) 516 = 0
  unfold entry
  simp only [show 4*(22+516/3) = 776 from rfl,
    show 1+516%3 = 1 from rfl, show 776+1 = 777 from rfl]
  exact SourceBlockSupport.column135_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 57 157 column135_tail (by decide) i)
#print axioms column135_tail
#print axioms column135_lower

end AspisV8R17.SourceMinor.LowerBlocks
