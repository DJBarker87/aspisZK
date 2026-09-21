import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport19

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column28_tail : orderedRows.drop 153 = SourceBlockSupport.column28_later := by decide
theorem column28_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 61) :
    orderedMinor half alpha a b c ⟨153+i.val, by omega⟩ 152 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (153+i.val) 0) 97 = 0
  unfold entry
  simp only [show 4*(22+97/3) = 216 from rfl,
    show 1+97%3 = 2 from rfl, show 216+2 = 218 from rfl]
  exact SourceBlockSupport.column28_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 153 61 column28_tail (by decide) i)
#print axioms column28_tail
#print axioms column28_lower

theorem column29_tail : orderedRows.drop 154 = SourceBlockSupport.column29_later := by decide
theorem column29_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 60) :
    orderedMinor half alpha a b c ⟨154+i.val, by omega⟩ 153 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (154+i.val) 0) 104 = 0
  unfold entry
  simp only [show 4*(22+104/3) = 224 from rfl,
    show 1+104%3 = 3 from rfl, show 224+3 = 227 from rfl]
  exact SourceBlockSupport.column29_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 154 60 column29_tail (by decide) i)
#print axioms column29_tail
#print axioms column29_lower

theorem column32_tail : orderedRows.drop 156 = SourceBlockSupport.column32_later := by decide
theorem column32_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 58) :
    orderedMinor half alpha a b c ⟨156+i.val, by omega⟩ 154 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (156+i.val) 0) 114 = 0
  unfold entry
  simp only [show 4*(22+114/3) = 240 from rfl,
    show 1+114%3 = 1 from rfl, show 240+1 = 241 from rfl]
  exact SourceBlockSupport.column32_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 156 58 column32_tail (by decide) i)
#print axioms column32_tail
#print axioms column32_lower

theorem column33_tail : orderedRows.drop 156 = SourceBlockSupport.column33_later := by decide
theorem column33_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 58) :
    orderedMinor half alpha a b c ⟨156+i.val, by omega⟩ 155 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (156+i.val) 0) 115 = 0
  unfold entry
  simp only [show 4*(22+115/3) = 240 from rfl,
    show 1+115%3 = 2 from rfl, show 240+2 = 242 from rfl]
  exact SourceBlockSupport.column33_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 156 58 column33_tail (by decide) i)
#print axioms column33_tail
#print axioms column33_lower

theorem column38_tail : orderedRows.drop 159 = SourceBlockSupport.column38_later := by decide
theorem column38_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 55) :
    orderedMinor half alpha a b c ⟨159+i.val, by omega⟩ 156 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (159+i.val) 0) 134 = 0
  unfold entry
  simp only [show 4*(22+134/3) = 264 from rfl,
    show 1+134%3 = 3 from rfl, show 264+3 = 267 from rfl]
  exact SourceBlockSupport.column38_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 159 55 column38_tail (by decide) i)
#print axioms column38_tail
#print axioms column38_lower

theorem column39_tail : orderedRows.drop 159 = SourceBlockSupport.column39_later := by decide
theorem column39_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 55) :
    orderedMinor half alpha a b c ⟨159+i.val, by omega⟩ 157 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (159+i.val) 0) 135 = 0
  unfold entry
  simp only [show 4*(22+135/3) = 268 from rfl,
    show 1+135%3 = 1 from rfl, show 268+1 = 269 from rfl]
  exact SourceBlockSupport.column39_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 159 55 column39_tail (by decide) i)
#print axioms column39_tail
#print axioms column39_lower

theorem column40_tail : orderedRows.drop 159 = SourceBlockSupport.column40_later := by decide
theorem column40_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 55) :
    orderedMinor half alpha a b c ⟨159+i.val, by omega⟩ 158 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (159+i.val) 0) 136 = 0
  unfold entry
  simp only [show 4*(22+136/3) = 268 from rfl,
    show 1+136%3 = 2 from rfl, show 268+2 = 270 from rfl]
  exact SourceBlockSupport.column40_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 159 55 column40_tail (by decide) i)
#print axioms column40_tail
#print axioms column40_lower

theorem column41_tail : orderedRows.drop 160 = SourceBlockSupport.column41_later := by decide
theorem column41_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 54) :
    orderedMinor half alpha a b c ⟨160+i.val, by omega⟩ 159 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (160+i.val) 0) 143 = 0
  unfold entry
  simp only [show 4*(22+143/3) = 276 from rfl,
    show 1+143%3 = 3 from rfl, show 276+3 = 279 from rfl]
  exact SourceBlockSupport.column41_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 160 54 column41_tail (by decide) i)
#print axioms column41_tail
#print axioms column41_lower

end AspisV8R17.SourceMinor.LowerBlocks
