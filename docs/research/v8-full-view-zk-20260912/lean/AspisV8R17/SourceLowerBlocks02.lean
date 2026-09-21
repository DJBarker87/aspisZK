import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport02

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column96_tail : orderedRows.drop 18 = SourceBlockSupport.column96_later := by decide
theorem column96_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 196) :
    orderedMinor half alpha a b c ⟨18+i.val, by omega⟩ 16 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (18+i.val) 0) 360 = 0
  unfold entry
  simp only [show 4*(22+360/3) = 568 from rfl,
    show 1+360%3 = 1 from rfl, show 568+1 = 569 from rfl]
  exact SourceBlockSupport.column96_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 18 196 column96_tail (by decide) i)
#print axioms column96_tail
#print axioms column96_lower

theorem column97_tail : orderedRows.drop 18 = SourceBlockSupport.column97_later := by decide
theorem column97_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 196) :
    orderedMinor half alpha a b c ⟨18+i.val, by omega⟩ 17 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (18+i.val) 0) 361 = 0
  unfold entry
  simp only [show 4*(22+361/3) = 568 from rfl,
    show 1+361%3 = 2 from rfl, show 568+2 = 570 from rfl]
  exact SourceBlockSupport.column97_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 18 196 column97_tail (by decide) i)
#print axioms column97_tail
#print axioms column97_lower

theorem column95_tail : orderedRows.drop 19 = SourceBlockSupport.column95_later := by decide
theorem column95_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 195) :
    orderedMinor half alpha a b c ⟨19+i.val, by omega⟩ 18 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (19+i.val) 0) 351 = 0
  unfold entry
  simp only [show 4*(22+351/3) = 556 from rfl,
    show 1+351%3 = 1 from rfl, show 556+1 = 557 from rfl]
  exact SourceBlockSupport.column95_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 19 195 column95_tail (by decide) i)
#print axioms column95_tail
#print axioms column95_lower

theorem column99_tail : orderedRows.drop 21 = SourceBlockSupport.column99_later := by decide
theorem column99_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 193) :
    orderedMinor half alpha a b c ⟨21+i.val, by omega⟩ 19 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (21+i.val) 0) 372 = 0
  unfold entry
  simp only [show 4*(22+372/3) = 584 from rfl,
    show 1+372%3 = 1 from rfl, show 584+1 = 585 from rfl]
  exact SourceBlockSupport.column99_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 21 193 column99_tail (by decide) i)
#print axioms column99_tail
#print axioms column99_lower

theorem column100_tail : orderedRows.drop 21 = SourceBlockSupport.column100_later := by decide
theorem column100_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 193) :
    orderedMinor half alpha a b c ⟨21+i.val, by omega⟩ 20 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (21+i.val) 0) 373 = 0
  unfold entry
  simp only [show 4*(22+373/3) = 584 from rfl,
    show 1+373%3 = 2 from rfl, show 584+2 = 586 from rfl]
  exact SourceBlockSupport.column100_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 21 193 column100_tail (by decide) i)
#print axioms column100_tail
#print axioms column100_lower

theorem column98_tail : orderedRows.drop 22 = SourceBlockSupport.column98_later := by decide
theorem column98_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 192) :
    orderedMinor half alpha a b c ⟨22+i.val, by omega⟩ 21 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (22+i.val) 0) 363 = 0
  unfold entry
  simp only [show 4*(22+363/3) = 572 from rfl,
    show 1+363%3 = 1 from rfl, show 572+1 = 573 from rfl]
  exact SourceBlockSupport.column98_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 22 192 column98_tail (by decide) i)
#print axioms column98_tail
#print axioms column98_lower

theorem column102_tail : orderedRows.drop 24 = SourceBlockSupport.column102_later := by decide
theorem column102_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 190) :
    orderedMinor half alpha a b c ⟨24+i.val, by omega⟩ 22 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (24+i.val) 0) 384 = 0
  unfold entry
  simp only [show 4*(22+384/3) = 600 from rfl,
    show 1+384%3 = 1 from rfl, show 600+1 = 601 from rfl]
  exact SourceBlockSupport.column102_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 24 190 column102_tail (by decide) i)
#print axioms column102_tail
#print axioms column102_lower

theorem column103_tail : orderedRows.drop 24 = SourceBlockSupport.column103_later := by decide
theorem column103_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 190) :
    orderedMinor half alpha a b c ⟨24+i.val, by omega⟩ 23 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (24+i.val) 0) 385 = 0
  unfold entry
  simp only [show 4*(22+385/3) = 600 from rfl,
    show 1+385%3 = 2 from rfl, show 600+2 = 602 from rfl]
  exact SourceBlockSupport.column103_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 24 190 column103_tail (by decide) i)
#print axioms column103_tail
#print axioms column103_lower

end AspisV8R17.SourceMinor.LowerBlocks
