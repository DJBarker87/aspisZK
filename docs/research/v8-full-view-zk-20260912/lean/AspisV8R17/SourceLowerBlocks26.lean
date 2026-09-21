import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport26

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column72_tail : orderedRows.drop 209 = SourceBlockSupport.column72_later := by decide
theorem column72_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 5) :
    orderedMinor half alpha a b c ⟨209+i.val, by omega⟩ 208 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (209+i.val) 0) 242 = 0
  unfold entry
  simp only [show 4*(22+242/3) = 408 from rfl,
    show 1+242%3 = 3 from rfl, show 408+3 = 411 from rfl]
  exact SourceBlockSupport.column72_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 209 5 column72_tail (by decide) i)
#print axioms column72_tail
#print axioms column72_lower

theorem column76_tail : orderedRows.drop 210 = SourceBlockSupport.column76_later := by decide
theorem column76_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 4) :
    orderedMinor half alpha a b c ⟨210+i.val, by omega⟩ 209 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (210+i.val) 0) 261 = 0
  unfold entry
  simp only [show 4*(22+261/3) = 436 from rfl,
    show 1+261%3 = 1 from rfl, show 436+1 = 437 from rfl]
  exact SourceBlockSupport.column76_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 210 4 column76_tail (by decide) i)
#print axioms column76_tail
#print axioms column76_lower

theorem column78_tail : orderedRows.drop 211 = SourceBlockSupport.column78_later := by decide
theorem column78_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 3) :
    orderedMinor half alpha a b c ⟨211+i.val, by omega⟩ 210 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (211+i.val) 0) 272 = 0
  unfold entry
  simp only [show 4*(22+272/3) = 448 from rfl,
    show 1+272%3 = 3 from rfl, show 448+3 = 451 from rfl]
  exact SourceBlockSupport.column78_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 211 3 column78_tail (by decide) i)
#print axioms column78_tail
#print axioms column78_lower

theorem column82_tail : orderedRows.drop 212 = SourceBlockSupport.column82_later := by decide
theorem column82_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 2) :
    orderedMinor half alpha a b c ⟨212+i.val, by omega⟩ 211 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (212+i.val) 0) 290 = 0
  unfold entry
  simp only [show 4*(22+290/3) = 472 from rfl,
    show 1+290%3 = 3 from rfl, show 472+3 = 475 from rfl]
  exact SourceBlockSupport.column82_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 212 2 column82_tail (by decide) i)
#print axioms column82_tail
#print axioms column82_lower

theorem column83_tail : orderedRows.drop 213 = SourceBlockSupport.column83_later := by decide
theorem column83_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 1) :
    orderedMinor half alpha a b c ⟨213+i.val, by omega⟩ 212 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (213+i.val) 0) 300 = 0
  unfold entry
  simp only [show 4*(22+300/3) = 488 from rfl,
    show 1+300%3 = 1 from rfl, show 488+1 = 489 from rfl]
  exact SourceBlockSupport.column83_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 213 1 column83_tail (by decide) i)
#print axioms column83_tail
#print axioms column83_lower

theorem column88_tail : orderedRows.drop 214 = SourceBlockSupport.column88_later := by decide
theorem column88_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 0) :
    orderedMinor half alpha a b c ⟨214+i.val, by omega⟩ 213 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (214+i.val) 0) 324 = 0
  unfold entry
  simp only [show 4*(22+324/3) = 520 from rfl,
    show 1+324%3 = 1 from rfl, show 520+1 = 521 from rfl]
  exact SourceBlockSupport.column88_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 214 0 column88_tail (by decide) i)
#print axioms column88_tail
#print axioms column88_lower

end AspisV8R17.SourceMinor.LowerBlocks
