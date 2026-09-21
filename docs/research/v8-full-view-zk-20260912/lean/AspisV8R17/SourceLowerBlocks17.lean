import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport17

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column208_tail : orderedRows.drop 137 = SourceBlockSupport.column208_later := by decide
theorem column208_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 77) :
    orderedMinor half alpha a b c ⟨137+i.val, by omega⟩ 136 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (137+i.val) 0) 689 = 0
  unfold entry
  simp only [show 4*(22+689/3) = 1004 from rfl,
    show 1+689%3 = 3 from rfl, show 1004+3 = 1007 from rfl]
  exact SourceBlockSupport.column208_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 137 77 column208_tail (by decide) i)
#print axioms column208_tail
#print axioms column208_lower

theorem column65_tail : orderedRows.drop 138 = SourceBlockSupport.column65_later := by decide
theorem column65_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 76) :
    orderedMinor half alpha a b c ⟨138+i.val, by omega⟩ 137 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (138+i.val) 0) 221 = 0
  unfold entry
  simp only [show 4*(22+221/3) = 380 from rfl,
    show 1+221%3 = 3 from rfl, show 380+3 = 383 from rfl]
  exact SourceBlockSupport.column65_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 138 76 column65_tail (by decide) i)
#print axioms column65_tail
#print axioms column65_lower

theorem column209_tail : orderedRows.drop 139 = SourceBlockSupport.column209_later := by decide
theorem column209_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 75) :
    orderedMinor half alpha a b c ⟨139+i.val, by omega⟩ 138 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (139+i.val) 0) 690 = 0
  unfold entry
  simp only [show 4*(22+690/3) = 1008 from rfl,
    show 1+690%3 = 1 from rfl, show 1008+1 = 1009 from rfl]
  exact SourceBlockSupport.column209_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 139 75 column209_tail (by decide) i)
#print axioms column209_tail
#print axioms column209_lower

theorem column210_tail : orderedRows.drop 140 = SourceBlockSupport.column210_later := by decide
theorem column210_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 74) :
    orderedMinor half alpha a b c ⟨140+i.val, by omega⟩ 139 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (140+i.val) 0) 692 = 0
  unfold entry
  simp only [show 4*(22+692/3) = 1008 from rfl,
    show 1+692%3 = 3 from rfl, show 1008+3 = 1011 from rfl]
  exact SourceBlockSupport.column210_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 140 74 column210_tail (by decide) i)
#print axioms column210_tail
#print axioms column210_lower

theorem column2_tail : orderedRows.drop 143 = SourceBlockSupport.column2_later := by decide
theorem column2_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 71) :
    orderedMinor half alpha a b c ⟨143+i.val, by omega⟩ 140 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (143+i.val) 0) 17 = 0
  unfold entry
  simp only [show 4*(22+17/3) = 108 from rfl,
    show 1+17%3 = 3 from rfl, show 108+3 = 111 from rfl]
  exact SourceBlockSupport.column2_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 143 71 column2_tail (by decide) i)
#print axioms column2_tail
#print axioms column2_lower

theorem column3_tail : orderedRows.drop 143 = SourceBlockSupport.column3_later := by decide
theorem column3_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 71) :
    orderedMinor half alpha a b c ⟨143+i.val, by omega⟩ 141 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (143+i.val) 0) 18 = 0
  unfold entry
  simp only [show 4*(22+18/3) = 112 from rfl,
    show 1+18%3 = 1 from rfl, show 112+1 = 113 from rfl]
  exact SourceBlockSupport.column3_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 143 71 column3_tail (by decide) i)
#print axioms column3_tail
#print axioms column3_lower

theorem column4_tail : orderedRows.drop 143 = SourceBlockSupport.column4_later := by decide
theorem column4_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 71) :
    orderedMinor half alpha a b c ⟨143+i.val, by omega⟩ 142 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (143+i.val) 0) 19 = 0
  unfold entry
  simp only [show 4*(22+19/3) = 112 from rfl,
    show 1+19%3 = 2 from rfl, show 112+2 = 114 from rfl]
  exact SourceBlockSupport.column4_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 143 71 column4_tail (by decide) i)
#print axioms column4_tail
#print axioms column4_lower

theorem column8_tail : orderedRows.drop 145 = SourceBlockSupport.column8_later := by decide
theorem column8_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 69) :
    orderedMinor half alpha a b c ⟨145+i.val, by omega⟩ 143 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (145+i.val) 0) 36 = 0
  unfold entry
  simp only [show 4*(22+36/3) = 136 from rfl,
    show 1+36%3 = 1 from rfl, show 136+1 = 137 from rfl]
  exact SourceBlockSupport.column8_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 145 69 column8_tail (by decide) i)
#print axioms column8_tail
#print axioms column8_lower

end AspisV8R17.SourceMinor.LowerBlocks
