import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport05

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column120_tail : orderedRows.drop 42 = SourceBlockSupport.column120_later := by decide
theorem column120_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 172) :
    orderedMinor half alpha a b c ⟨42+i.val, by omega⟩ 40 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (42+i.val) 0) 456 = 0
  unfold entry
  simp only [show 4*(22+456/3) = 696 from rfl,
    show 1+456%3 = 1 from rfl, show 696+1 = 697 from rfl]
  exact SourceBlockSupport.column120_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 42 172 column120_tail (by decide) i)
#print axioms column120_tail
#print axioms column120_lower

theorem column121_tail : orderedRows.drop 42 = SourceBlockSupport.column121_later := by decide
theorem column121_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 172) :
    orderedMinor half alpha a b c ⟨42+i.val, by omega⟩ 41 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (42+i.val) 0) 457 = 0
  unfold entry
  simp only [show 4*(22+457/3) = 696 from rfl,
    show 1+457%3 = 2 from rfl, show 696+2 = 698 from rfl]
  exact SourceBlockSupport.column121_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 42 172 column121_tail (by decide) i)
#print axioms column121_tail
#print axioms column121_lower

theorem column119_tail : orderedRows.drop 43 = SourceBlockSupport.column119_later := by decide
theorem column119_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 171) :
    orderedMinor half alpha a b c ⟨43+i.val, by omega⟩ 42 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (43+i.val) 0) 447 = 0
  unfold entry
  simp only [show 4*(22+447/3) = 684 from rfl,
    show 1+447%3 = 1 from rfl, show 684+1 = 685 from rfl]
  exact SourceBlockSupport.column119_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 43 171 column119_tail (by decide) i)
#print axioms column119_tail
#print axioms column119_lower

theorem column123_tail : orderedRows.drop 45 = SourceBlockSupport.column123_later := by decide
theorem column123_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 169) :
    orderedMinor half alpha a b c ⟨45+i.val, by omega⟩ 43 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (45+i.val) 0) 468 = 0
  unfold entry
  simp only [show 4*(22+468/3) = 712 from rfl,
    show 1+468%3 = 1 from rfl, show 712+1 = 713 from rfl]
  exact SourceBlockSupport.column123_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 45 169 column123_tail (by decide) i)
#print axioms column123_tail
#print axioms column123_lower

theorem column124_tail : orderedRows.drop 45 = SourceBlockSupport.column124_later := by decide
theorem column124_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 169) :
    orderedMinor half alpha a b c ⟨45+i.val, by omega⟩ 44 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (45+i.val) 0) 469 = 0
  unfold entry
  simp only [show 4*(22+469/3) = 712 from rfl,
    show 1+469%3 = 2 from rfl, show 712+2 = 714 from rfl]
  exact SourceBlockSupport.column124_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 45 169 column124_tail (by decide) i)
#print axioms column124_tail
#print axioms column124_lower

theorem column122_tail : orderedRows.drop 46 = SourceBlockSupport.column122_later := by decide
theorem column122_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 168) :
    orderedMinor half alpha a b c ⟨46+i.val, by omega⟩ 45 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (46+i.val) 0) 459 = 0
  unfold entry
  simp only [show 4*(22+459/3) = 700 from rfl,
    show 1+459%3 = 1 from rfl, show 700+1 = 701 from rfl]
  exact SourceBlockSupport.column122_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 46 168 column122_tail (by decide) i)
#print axioms column122_tail
#print axioms column122_lower

theorem column126_tail : orderedRows.drop 48 = SourceBlockSupport.column126_later := by decide
theorem column126_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 166) :
    orderedMinor half alpha a b c ⟨48+i.val, by omega⟩ 46 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (48+i.val) 0) 480 = 0
  unfold entry
  simp only [show 4*(22+480/3) = 728 from rfl,
    show 1+480%3 = 1 from rfl, show 728+1 = 729 from rfl]
  exact SourceBlockSupport.column126_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 48 166 column126_tail (by decide) i)
#print axioms column126_tail
#print axioms column126_lower

theorem column127_tail : orderedRows.drop 48 = SourceBlockSupport.column127_later := by decide
theorem column127_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 166) :
    orderedMinor half alpha a b c ⟨48+i.val, by omega⟩ 47 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (48+i.val) 0) 481 = 0
  unfold entry
  simp only [show 4*(22+481/3) = 728 from rfl,
    show 1+481%3 = 2 from rfl, show 728+2 = 730 from rfl]
  exact SourceBlockSupport.column127_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 48 166 column127_tail (by decide) i)
#print axioms column127_tail
#print axioms column127_lower

end AspisV8R17.SourceMinor.LowerBlocks
