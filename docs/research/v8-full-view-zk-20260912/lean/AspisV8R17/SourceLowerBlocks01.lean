import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport01

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column84_tail : orderedRows.drop 9 = SourceBlockSupport.column84_later := by decide
theorem column84_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 205) :
    orderedMinor half alpha a b c ⟨9+i.val, by omega⟩ 8 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (9+i.val) 0) 303 = 0
  unfold entry
  simp only [show 4*(22+303/3) = 492 from rfl,
    show 1+303%3 = 1 from rfl, show 492+1 = 493 from rfl]
  exact SourceBlockSupport.column84_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 9 205 column84_tail (by decide) i)
#print axioms column84_tail
#print axioms column84_lower

theorem column87_tail : orderedRows.drop 10 = SourceBlockSupport.column87_later := by decide
theorem column87_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 204) :
    orderedMinor half alpha a b c ⟨10+i.val, by omega⟩ 9 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (10+i.val) 0) 315 = 0
  unfold entry
  simp only [show 4*(22+315/3) = 508 from rfl,
    show 1+315%3 = 1 from rfl, show 508+1 = 509 from rfl]
  exact SourceBlockSupport.column87_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 10 204 column87_tail (by decide) i)
#print axioms column87_tail
#print axioms column87_lower

theorem column90_tail : orderedRows.drop 12 = SourceBlockSupport.column90_later := by decide
theorem column90_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 202) :
    orderedMinor half alpha a b c ⟨12+i.val, by omega⟩ 10 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (12+i.val) 0) 336 = 0
  unfold entry
  simp only [show 4*(22+336/3) = 536 from rfl,
    show 1+336%3 = 1 from rfl, show 536+1 = 537 from rfl]
  exact SourceBlockSupport.column90_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 12 202 column90_tail (by decide) i)
#print axioms column90_tail
#print axioms column90_lower

theorem column91_tail : orderedRows.drop 12 = SourceBlockSupport.column91_later := by decide
theorem column91_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 202) :
    orderedMinor half alpha a b c ⟨12+i.val, by omega⟩ 11 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (12+i.val) 0) 337 = 0
  unfold entry
  simp only [show 4*(22+337/3) = 536 from rfl,
    show 1+337%3 = 2 from rfl, show 536+2 = 538 from rfl]
  exact SourceBlockSupport.column91_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 12 202 column91_tail (by decide) i)
#print axioms column91_tail
#print axioms column91_lower

theorem column89_tail : orderedRows.drop 13 = SourceBlockSupport.column89_later := by decide
theorem column89_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 201) :
    orderedMinor half alpha a b c ⟨13+i.val, by omega⟩ 12 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (13+i.val) 0) 327 = 0
  unfold entry
  simp only [show 4*(22+327/3) = 524 from rfl,
    show 1+327%3 = 1 from rfl, show 524+1 = 525 from rfl]
  exact SourceBlockSupport.column89_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 13 201 column89_tail (by decide) i)
#print axioms column89_tail
#print axioms column89_lower

theorem column93_tail : orderedRows.drop 15 = SourceBlockSupport.column93_later := by decide
theorem column93_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 199) :
    orderedMinor half alpha a b c ⟨15+i.val, by omega⟩ 13 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (15+i.val) 0) 348 = 0
  unfold entry
  simp only [show 4*(22+348/3) = 552 from rfl,
    show 1+348%3 = 1 from rfl, show 552+1 = 553 from rfl]
  exact SourceBlockSupport.column93_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 15 199 column93_tail (by decide) i)
#print axioms column93_tail
#print axioms column93_lower

theorem column94_tail : orderedRows.drop 15 = SourceBlockSupport.column94_later := by decide
theorem column94_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 199) :
    orderedMinor half alpha a b c ⟨15+i.val, by omega⟩ 14 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (15+i.val) 0) 349 = 0
  unfold entry
  simp only [show 4*(22+349/3) = 552 from rfl,
    show 1+349%3 = 2 from rfl, show 552+2 = 554 from rfl]
  exact SourceBlockSupport.column94_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 15 199 column94_tail (by decide) i)
#print axioms column94_tail
#print axioms column94_lower

theorem column92_tail : orderedRows.drop 16 = SourceBlockSupport.column92_later := by decide
theorem column92_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 198) :
    orderedMinor half alpha a b c ⟨16+i.val, by omega⟩ 15 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (16+i.val) 0) 339 = 0
  unfold entry
  simp only [show 4*(22+339/3) = 540 from rfl,
    show 1+339%3 = 1 from rfl, show 540+1 = 541 from rfl]
  exact SourceBlockSupport.column92_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 16 198 column92_tail (by decide) i)
#print axioms column92_tail
#print axioms column92_lower

end AspisV8R17.SourceMinor.LowerBlocks
