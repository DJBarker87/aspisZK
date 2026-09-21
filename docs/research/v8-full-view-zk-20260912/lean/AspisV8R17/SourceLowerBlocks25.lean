import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport25

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column0_tail : orderedRows.drop 201 = SourceBlockSupport.column0_later := by decide
theorem column0_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 13) :
    orderedMinor half alpha a b c ⟨201+i.val, by omega⟩ 200 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (201+i.val) 0) 6 = 0
  unfold entry
  simp only [show 4*(22+6/3) = 96 from rfl,
    show 1+6%3 = 1 from rfl, show 96+1 = 97 from rfl]
  exact SourceBlockSupport.column0_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 201 13 column0_tail (by decide) i)
#print axioms column0_tail
#print axioms column0_lower

theorem column1_tail : orderedRows.drop 202 = SourceBlockSupport.column1_later := by decide
theorem column1_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 12) :
    orderedMinor half alpha a b c ⟨202+i.val, by omega⟩ 201 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (202+i.val) 0) 8 = 0
  unfold entry
  simp only [show 4*(22+8/3) = 96 from rfl,
    show 1+8%3 = 3 from rfl, show 96+3 = 99 from rfl]
  exact SourceBlockSupport.column1_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 202 12 column1_tail (by decide) i)
#print axioms column1_tail
#print axioms column1_lower

theorem column10_tail : orderedRows.drop 203 = SourceBlockSupport.column10_later := by decide
theorem column10_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 11) :
    orderedMinor half alpha a b c ⟨203+i.val, by omega⟩ 202 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (203+i.val) 0) 38 = 0
  unfold entry
  simp only [show 4*(22+38/3) = 136 from rfl,
    show 1+38%3 = 3 from rfl, show 136+3 = 139 from rfl]
  exact SourceBlockSupport.column10_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 203 11 column10_tail (by decide) i)
#print axioms column10_tail
#print axioms column10_lower

theorem column34_tail : orderedRows.drop 204 = SourceBlockSupport.column34_later := by decide
theorem column34_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 10) :
    orderedMinor half alpha a b c ⟨204+i.val, by omega⟩ 203 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (204+i.val) 0) 116 = 0
  unfold entry
  simp only [show 4*(22+116/3) = 240 from rfl,
    show 1+116%3 = 3 from rfl, show 240+3 = 243 from rfl]
  exact SourceBlockSupport.column34_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 204 10 column34_tail (by decide) i)
#print axioms column34_tail
#print axioms column34_lower

theorem column46_tail : orderedRows.drop 205 = SourceBlockSupport.column46_later := by decide
theorem column46_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 9) :
    orderedMinor half alpha a b c ⟨205+i.val, by omega⟩ 204 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (205+i.val) 0) 155 = 0
  unfold entry
  simp only [show 4*(22+155/3) = 292 from rfl,
    show 1+155%3 = 3 from rfl, show 292+3 = 295 from rfl]
  exact SourceBlockSupport.column46_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 205 9 column46_tail (by decide) i)
#print axioms column46_tail
#print axioms column46_lower

theorem column58_tail : orderedRows.drop 206 = SourceBlockSupport.column58_later := by decide
theorem column58_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 8) :
    orderedMinor half alpha a b c ⟨206+i.val, by omega⟩ 205 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (206+i.val) 0) 194 = 0
  unfold entry
  simp only [show 4*(22+194/3) = 344 from rfl,
    show 1+194%3 = 3 from rfl, show 344+3 = 347 from rfl]
  exact SourceBlockSupport.column58_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 206 8 column58_tail (by decide) i)
#print axioms column58_tail
#print axioms column58_lower

theorem column70_tail : orderedRows.drop 207 = SourceBlockSupport.column70_later := by decide
theorem column70_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 7) :
    orderedMinor half alpha a b c ⟨207+i.val, by omega⟩ 206 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (207+i.val) 0) 233 = 0
  unfold entry
  simp only [show 4*(22+233/3) = 396 from rfl,
    show 1+233%3 = 3 from rfl, show 396+3 = 399 from rfl]
  exact SourceBlockSupport.column70_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 207 7 column70_tail (by decide) i)
#print axioms column70_tail
#print axioms column70_lower

theorem column71_tail : orderedRows.drop 208 = SourceBlockSupport.column71_later := by decide
theorem column71_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 6) :
    orderedMinor half alpha a b c ⟨208+i.val, by omega⟩ 207 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (208+i.val) 0) 240 = 0
  unfold entry
  simp only [show 4*(22+240/3) = 408 from rfl,
    show 1+240%3 = 1 from rfl, show 408+1 = 409 from rfl]
  exact SourceBlockSupport.column71_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 208 6 column71_tail (by decide) i)
#print axioms column71_tail
#print axioms column71_lower

end AspisV8R17.SourceMinor.LowerBlocks
