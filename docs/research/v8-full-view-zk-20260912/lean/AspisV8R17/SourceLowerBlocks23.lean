import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport23

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column31_tail : orderedRows.drop 185 = SourceBlockSupport.column31_later := by decide
theorem column31_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 29) :
    orderedMinor half alpha a b c ⟨185+i.val, by omega⟩ 184 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (185+i.val) 0) 106 = 0
  unfold entry
  simp only [show 4*(22+106/3) = 228 from rfl,
    show 1+106%3 = 2 from rfl, show 228+2 = 230 from rfl]
  exact SourceBlockSupport.column31_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 185 29 column31_tail (by decide) i)
#print axioms column31_tail
#print axioms column31_lower

theorem column42_tail : orderedRows.drop 187 = SourceBlockSupport.column42_later := by decide
theorem column42_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 27) :
    orderedMinor half alpha a b c ⟨187+i.val, by omega⟩ 185 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (187+i.val) 0) 144 = 0
  unfold entry
  simp only [show 4*(22+144/3) = 280 from rfl,
    show 1+144%3 = 1 from rfl, show 280+1 = 281 from rfl]
  exact SourceBlockSupport.column42_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 187 27 column42_tail (by decide) i)
#print axioms column42_tail
#print axioms column42_lower

theorem column43_tail : orderedRows.drop 187 = SourceBlockSupport.column43_later := by decide
theorem column43_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 27) :
    orderedMinor half alpha a b c ⟨187+i.val, by omega⟩ 186 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (187+i.val) 0) 145 = 0
  unfold entry
  simp only [show 4*(22+145/3) = 280 from rfl,
    show 1+145%3 = 2 from rfl, show 280+2 = 282 from rfl]
  exact SourceBlockSupport.column43_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 187 27 column43_tail (by decide) i)
#print axioms column43_tail
#print axioms column43_lower

theorem column48_tail : orderedRows.drop 189 = SourceBlockSupport.column48_later := by decide
theorem column48_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 25) :
    orderedMinor half alpha a b c ⟨189+i.val, by omega⟩ 187 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (189+i.val) 0) 164 = 0
  unfold entry
  simp only [show 4*(22+164/3) = 304 from rfl,
    show 1+164%3 = 3 from rfl, show 304+3 = 307 from rfl]
  exact SourceBlockSupport.column48_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 189 25 column48_tail (by decide) i)
#print axioms column48_tail
#print axioms column48_lower

theorem column49_tail : orderedRows.drop 189 = SourceBlockSupport.column49_later := by decide
theorem column49_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 25) :
    orderedMinor half alpha a b c ⟨189+i.val, by omega⟩ 188 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (189+i.val) 0) 165 = 0
  unfold entry
  simp only [show 4*(22+165/3) = 308 from rfl,
    show 1+165%3 = 1 from rfl, show 308+1 = 309 from rfl]
  exact SourceBlockSupport.column49_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 189 25 column49_tail (by decide) i)
#print axioms column49_tail
#print axioms column49_lower

theorem column54_tail : orderedRows.drop 191 = SourceBlockSupport.column54_later := by decide
theorem column54_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 23) :
    orderedMinor half alpha a b c ⟨191+i.val, by omega⟩ 189 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (191+i.val) 0) 183 = 0
  unfold entry
  simp only [show 4*(22+183/3) = 332 from rfl,
    show 1+183%3 = 1 from rfl, show 332+1 = 333 from rfl]
  exact SourceBlockSupport.column54_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 191 23 column54_tail (by decide) i)
#print axioms column54_tail
#print axioms column54_lower

theorem column55_tail : orderedRows.drop 191 = SourceBlockSupport.column55_later := by decide
theorem column55_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 23) :
    orderedMinor half alpha a b c ⟨191+i.val, by omega⟩ 190 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (191+i.val) 0) 184 = 0
  unfold entry
  simp only [show 4*(22+184/3) = 332 from rfl,
    show 1+184%3 = 2 from rfl, show 332+2 = 334 from rfl]
  exact SourceBlockSupport.column55_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 191 23 column55_tail (by decide) i)
#print axioms column55_tail
#print axioms column55_lower

theorem column60_tail : orderedRows.drop 193 = SourceBlockSupport.column60_later := by decide
theorem column60_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 21) :
    orderedMinor half alpha a b c ⟨193+i.val, by omega⟩ 191 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (193+i.val) 0) 203 = 0
  unfold entry
  simp only [show 4*(22+203/3) = 356 from rfl,
    show 1+203%3 = 3 from rfl, show 356+3 = 359 from rfl]
  exact SourceBlockSupport.column60_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 193 21 column60_tail (by decide) i)
#print axioms column60_tail
#print axioms column60_lower

end AspisV8R17.SourceMinor.LowerBlocks
