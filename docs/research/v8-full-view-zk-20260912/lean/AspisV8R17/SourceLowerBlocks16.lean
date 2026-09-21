import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport16

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column36_tail : orderedRows.drop 130 = SourceBlockSupport.column36_later := by decide
theorem column36_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 84) :
    orderedMinor half alpha a b c ⟨130+i.val, by omega⟩ 128 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (130+i.val) 0) 125 = 0
  unfold entry
  simp only [show 4*(22+125/3) = 252 from rfl,
    show 1+125%3 = 3 from rfl, show 252+3 = 255 from rfl]
  exact SourceBlockSupport.column36_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 130 84 column36_tail (by decide) i)
#print axioms column36_tail
#print axioms column36_lower

theorem column37_tail : orderedRows.drop 130 = SourceBlockSupport.column37_later := by decide
theorem column37_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 84) :
    orderedMinor half alpha a b c ⟨130+i.val, by omega⟩ 129 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (130+i.val) 0) 126 = 0
  unfold entry
  simp only [show 4*(22+126/3) = 256 from rfl,
    show 1+126%3 = 1 from rfl, show 256+1 = 257 from rfl]
  exact SourceBlockSupport.column37_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 130 84 column37_tail (by decide) i)
#print axioms column37_tail
#print axioms column37_lower

theorem column205_tail : orderedRows.drop 133 = SourceBlockSupport.column205_later := by decide
theorem column205_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 81) :
    orderedMinor half alpha a b c ⟨133+i.val, by omega⟩ 130 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (133+i.val) 0) 686 = 0
  unfold entry
  simp only [show 4*(22+686/3) = 1000 from rfl,
    show 1+686%3 = 3 from rfl, show 1000+3 = 1003 from rfl]
  exact SourceBlockSupport.column205_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 133 81 column205_tail (by decide) i)
#print axioms column205_tail
#print axioms column205_lower

theorem column206_tail : orderedRows.drop 133 = SourceBlockSupport.column206_later := by decide
theorem column206_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 81) :
    orderedMinor half alpha a b c ⟨133+i.val, by omega⟩ 131 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (133+i.val) 0) 687 = 0
  unfold entry
  simp only [show 4*(22+687/3) = 1004 from rfl,
    show 1+687%3 = 1 from rfl, show 1004+1 = 1005 from rfl]
  exact SourceBlockSupport.column206_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 133 81 column206_tail (by decide) i)
#print axioms column206_tail
#print axioms column206_lower

theorem column207_tail : orderedRows.drop 133 = SourceBlockSupport.column207_later := by decide
theorem column207_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 81) :
    orderedMinor half alpha a b c ⟨133+i.val, by omega⟩ 132 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (133+i.val) 0) 688 = 0
  unfold entry
  simp only [show 4*(22+688/3) = 1004 from rfl,
    show 1+688%3 = 2 from rfl, show 1004+2 = 1006 from rfl]
  exact SourceBlockSupport.column207_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 133 81 column207_tail (by decide) i)
#print axioms column207_tail
#print axioms column207_lower

theorem column50_tail : orderedRows.drop 136 = SourceBlockSupport.column50_later := by decide
theorem column50_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 78) :
    orderedMinor half alpha a b c ⟨136+i.val, by omega⟩ 133 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (136+i.val) 0) 173 = 0
  unfold entry
  simp only [show 4*(22+173/3) = 316 from rfl,
    show 1+173%3 = 3 from rfl, show 316+3 = 319 from rfl]
  exact SourceBlockSupport.column50_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 136 78 column50_tail (by decide) i)
#print axioms column50_tail
#print axioms column50_lower

theorem column51_tail : orderedRows.drop 136 = SourceBlockSupport.column51_later := by decide
theorem column51_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 78) :
    orderedMinor half alpha a b c ⟨136+i.val, by omega⟩ 134 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (136+i.val) 0) 174 = 0
  unfold entry
  simp only [show 4*(22+174/3) = 320 from rfl,
    show 1+174%3 = 1 from rfl, show 320+1 = 321 from rfl]
  exact SourceBlockSupport.column51_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 136 78 column51_tail (by decide) i)
#print axioms column51_tail
#print axioms column51_lower

theorem column52_tail : orderedRows.drop 136 = SourceBlockSupport.column52_later := by decide
theorem column52_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 78) :
    orderedMinor half alpha a b c ⟨136+i.val, by omega⟩ 135 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (136+i.val) 0) 175 = 0
  unfold entry
  simp only [show 4*(22+175/3) = 320 from rfl,
    show 1+175%3 = 2 from rfl, show 320+2 = 322 from rfl]
  exact SourceBlockSupport.column52_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 136 78 column52_tail (by decide) i)
#print axioms column52_tail
#print axioms column52_lower

end AspisV8R17.SourceMinor.LowerBlocks
