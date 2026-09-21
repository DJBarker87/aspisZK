import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport00

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column5_tail : orderedRows.drop 1 = SourceBlockSupport.column5_later := by decide
theorem column5_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 213) :
    orderedMinor half alpha a b c ⟨1+i.val, by omega⟩ 0 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (1+i.val) 0) 26 = 0
  unfold entry
  simp only [show 4*(22+26/3) = 120 from rfl,
    show 1+26%3 = 3 from rfl, show 120+3 = 123 from rfl]
  exact SourceBlockSupport.column5_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 1 213 column5_tail (by decide) i)
#print axioms column5_tail
#print axioms column5_lower

theorem column6_tail : orderedRows.drop 3 = SourceBlockSupport.column6_later := by decide
theorem column6_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 211) :
    orderedMinor half alpha a b c ⟨3+i.val, by omega⟩ 1 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (3+i.val) 0) 27 = 0
  unfold entry
  simp only [show 4*(22+27/3) = 124 from rfl,
    show 1+27%3 = 1 from rfl, show 124+1 = 125 from rfl]
  exact SourceBlockSupport.column6_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 3 211 column6_tail (by decide) i)
#print axioms column6_tail
#print axioms column6_lower

theorem column7_tail : orderedRows.drop 3 = SourceBlockSupport.column7_later := by decide
theorem column7_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 211) :
    orderedMinor half alpha a b c ⟨3+i.val, by omega⟩ 2 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (3+i.val) 0) 28 = 0
  unfold entry
  simp only [show 4*(22+28/3) = 124 from rfl,
    show 1+28%3 = 2 from rfl, show 124+2 = 126 from rfl]
  exact SourceBlockSupport.column7_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 3 211 column7_tail (by decide) i)
#print axioms column7_tail
#print axioms column7_lower

theorem column20_tail : orderedRows.drop 5 = SourceBlockSupport.column20_later := by decide
theorem column20_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 209) :
    orderedMinor half alpha a b c ⟨5+i.val, by omega⟩ 3 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (5+i.val) 0) 75 = 0
  unfold entry
  simp only [show 4*(22+75/3) = 188 from rfl,
    show 1+75%3 = 1 from rfl, show 188+1 = 189 from rfl]
  exact SourceBlockSupport.column20_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 5 209 column20_tail (by decide) i)
#print axioms column20_tail
#print axioms column20_lower

theorem column21_tail : orderedRows.drop 5 = SourceBlockSupport.column21_later := by decide
theorem column21_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 209) :
    orderedMinor half alpha a b c ⟨5+i.val, by omega⟩ 4 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (5+i.val) 0) 76 = 0
  unfold entry
  simp only [show 4*(22+76/3) = 188 from rfl,
    show 1+76%3 = 2 from rfl, show 188+2 = 190 from rfl]
  exact SourceBlockSupport.column21_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 5 209 column21_tail (by decide) i)
#print axioms column21_tail
#print axioms column21_lower

theorem column35_tail : orderedRows.drop 6 = SourceBlockSupport.column35_later := by decide
theorem column35_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 208) :
    orderedMinor half alpha a b c ⟨6+i.val, by omega⟩ 5 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (6+i.val) 0) 123 = 0
  unfold entry
  simp only [show 4*(22+123/3) = 252 from rfl,
    show 1+123%3 = 1 from rfl, show 252+1 = 253 from rfl]
  exact SourceBlockSupport.column35_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 6 208 column35_tail (by decide) i)
#print axioms column35_tail
#print axioms column35_lower

theorem column85_tail : orderedRows.drop 8 = SourceBlockSupport.column85_later := by decide
theorem column85_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 206) :
    orderedMinor half alpha a b c ⟨8+i.val, by omega⟩ 6 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (8+i.val) 0) 312 = 0
  unfold entry
  simp only [show 4*(22+312/3) = 504 from rfl,
    show 1+312%3 = 1 from rfl, show 504+1 = 505 from rfl]
  exact SourceBlockSupport.column85_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 8 206 column85_tail (by decide) i)
#print axioms column85_tail
#print axioms column85_lower

theorem column86_tail : orderedRows.drop 8 = SourceBlockSupport.column86_later := by decide
theorem column86_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 206) :
    orderedMinor half alpha a b c ⟨8+i.val, by omega⟩ 7 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (8+i.val) 0) 313 = 0
  unfold entry
  simp only [show 4*(22+313/3) = 504 from rfl,
    show 1+313%3 = 2 from rfl, show 504+2 = 506 from rfl]
  exact SourceBlockSupport.column86_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 8 206 column86_tail (by decide) i)
#print axioms column86_tail
#print axioms column86_lower

end AspisV8R17.SourceMinor.LowerBlocks
