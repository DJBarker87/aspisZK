import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport24

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column61_tail : orderedRows.drop 193 = SourceBlockSupport.column61_later := by decide
theorem column61_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 21) :
    orderedMinor half alpha a b c ⟨193+i.val, by omega⟩ 192 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (193+i.val) 0) 204 = 0
  unfold entry
  simp only [show 4*(22+204/3) = 360 from rfl,
    show 1+204%3 = 1 from rfl, show 360+1 = 361 from rfl]
  exact SourceBlockSupport.column61_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 193 21 column61_tail (by decide) i)
#print axioms column61_tail
#print axioms column61_lower

theorem column66_tail : orderedRows.drop 195 = SourceBlockSupport.column66_later := by decide
theorem column66_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 19) :
    orderedMinor half alpha a b c ⟨195+i.val, by omega⟩ 193 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (195+i.val) 0) 222 = 0
  unfold entry
  simp only [show 4*(22+222/3) = 384 from rfl,
    show 1+222%3 = 1 from rfl, show 384+1 = 385 from rfl]
  exact SourceBlockSupport.column66_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 195 19 column66_tail (by decide) i)
#print axioms column66_tail
#print axioms column66_lower

theorem column67_tail : orderedRows.drop 195 = SourceBlockSupport.column67_later := by decide
theorem column67_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 19) :
    orderedMinor half alpha a b c ⟨195+i.val, by omega⟩ 194 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (195+i.val) 0) 223 = 0
  unfold entry
  simp only [show 4*(22+223/3) = 384 from rfl,
    show 1+223%3 = 2 from rfl, show 384+2 = 386 from rfl]
  exact SourceBlockSupport.column67_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 195 19 column67_tail (by decide) i)
#print axioms column67_tail
#print axioms column67_lower

theorem column77_tail : orderedRows.drop 196 = SourceBlockSupport.column77_later := by decide
theorem column77_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 18) :
    orderedMinor half alpha a b c ⟨196+i.val, by omega⟩ 195 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (196+i.val) 0) 270 = 0
  unfold entry
  simp only [show 4*(22+270/3) = 448 from rfl,
    show 1+270%3 = 1 from rfl, show 448+1 = 449 from rfl]
  exact SourceBlockSupport.column77_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 196 18 column77_tail (by decide) i)
#print axioms column77_tail
#print axioms column77_lower

theorem column80_tail : orderedRows.drop 198 = SourceBlockSupport.column80_later := by decide
theorem column80_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 16) :
    orderedMinor half alpha a b c ⟨198+i.val, by omega⟩ 196 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (198+i.val) 0) 281 = 0
  unfold entry
  simp only [show 4*(22+281/3) = 460 from rfl,
    show 1+281%3 = 3 from rfl, show 460+3 = 463 from rfl]
  exact SourceBlockSupport.column80_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 198 16 column80_tail (by decide) i)
#print axioms column80_tail
#print axioms column80_lower

theorem column81_tail : orderedRows.drop 198 = SourceBlockSupport.column81_later := by decide
theorem column81_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 16) :
    orderedMinor half alpha a b c ⟨198+i.val, by omega⟩ 197 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (198+i.val) 0) 282 = 0
  unfold entry
  simp only [show 4*(22+282/3) = 464 from rfl,
    show 1+282%3 = 1 from rfl, show 464+1 = 465 from rfl]
  exact SourceBlockSupport.column81_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 198 16 column81_tail (by decide) i)
#print axioms column81_tail
#print axioms column81_lower

theorem column212_tail : orderedRows.drop 200 = SourceBlockSupport.column212_later := by decide
theorem column212_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 14) :
    orderedMinor half alpha a b c ⟨200+i.val, by omega⟩ 198 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (200+i.val) 0) 695 = 0
  unfold entry
  simp only [show 4*(22+695/3) = 1012 from rfl,
    show 1+695%3 = 3 from rfl, show 1012+3 = 1015 from rfl]
  exact SourceBlockSupport.column212_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 200 14 column212_tail (by decide) i)
#print axioms column212_tail
#print axioms column212_lower

theorem column213_tail : orderedRows.drop 200 = SourceBlockSupport.column213_later := by decide
theorem column213_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 14) :
    orderedMinor half alpha a b c ⟨200+i.val, by omega⟩ 199 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (200+i.val) 0) 696 = 0
  unfold entry
  simp only [show 4*(22+696/3) = 1016 from rfl,
    show 1+696%3 = 1 from rfl, show 1016+1 = 1017 from rfl]
  exact SourceBlockSupport.column213_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 200 14 column213_tail (by decide) i)
#print axioms column213_tail
#print axioms column213_lower

end AspisV8R17.SourceMinor.LowerBlocks
