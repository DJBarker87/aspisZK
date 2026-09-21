import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport18

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column9_tail : orderedRows.drop 145 = SourceBlockSupport.column9_later := by decide
theorem column9_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 69) :
    orderedMinor half alpha a b c ⟨145+i.val, by omega⟩ 144 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (145+i.val) 0) 37 = 0
  unfold entry
  simp only [show 4*(22+37/3) = 136 from rfl,
    show 1+37%3 = 2 from rfl, show 136+2 = 138 from rfl]
  exact SourceBlockSupport.column9_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 145 69 column9_tail (by decide) i)
#print axioms column9_tail
#print axioms column9_lower

theorem column11_tail : orderedRows.drop 146 = SourceBlockSupport.column11_later := by decide
theorem column11_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 68) :
    orderedMinor half alpha a b c ⟨146+i.val, by omega⟩ 145 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (146+i.val) 0) 45 = 0
  unfold entry
  simp only [show 4*(22+45/3) = 148 from rfl,
    show 1+45%3 = 1 from rfl, show 148+1 = 149 from rfl]
  exact SourceBlockSupport.column11_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 146 68 column11_tail (by decide) i)
#print axioms column11_tail
#print axioms column11_lower

theorem column14_tail : orderedRows.drop 149 = SourceBlockSupport.column14_later := by decide
theorem column14_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 65) :
    orderedMinor half alpha a b c ⟨149+i.val, by omega⟩ 146 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (149+i.val) 0) 56 = 0
  unfold entry
  simp only [show 4*(22+56/3) = 160 from rfl,
    show 1+56%3 = 3 from rfl, show 160+3 = 163 from rfl]
  exact SourceBlockSupport.column14_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 149 65 column14_tail (by decide) i)
#print axioms column14_tail
#print axioms column14_lower

theorem column15_tail : orderedRows.drop 149 = SourceBlockSupport.column15_later := by decide
theorem column15_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 65) :
    orderedMinor half alpha a b c ⟨149+i.val, by omega⟩ 147 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (149+i.val) 0) 57 = 0
  unfold entry
  simp only [show 4*(22+57/3) = 164 from rfl,
    show 1+57%3 = 1 from rfl, show 164+1 = 165 from rfl]
  exact SourceBlockSupport.column15_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 149 65 column15_tail (by decide) i)
#print axioms column15_tail
#print axioms column15_lower

theorem column16_tail : orderedRows.drop 149 = SourceBlockSupport.column16_later := by decide
theorem column16_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 65) :
    orderedMinor half alpha a b c ⟨149+i.val, by omega⟩ 148 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (149+i.val) 0) 58 = 0
  unfold entry
  simp only [show 4*(22+58/3) = 164 from rfl,
    show 1+58%3 = 2 from rfl, show 164+2 = 166 from rfl]
  exact SourceBlockSupport.column16_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 149 65 column16_tail (by decide) i)
#print axioms column16_tail
#print axioms column16_lower

theorem column23_tail : orderedRows.drop 150 = SourceBlockSupport.column23_later := by decide
theorem column23_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 64) :
    orderedMinor half alpha a b c ⟨150+i.val, by omega⟩ 149 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (150+i.val) 0) 84 = 0
  unfold entry
  simp only [show 4*(22+84/3) = 200 from rfl,
    show 1+84%3 = 1 from rfl, show 200+1 = 201 from rfl]
  exact SourceBlockSupport.column23_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 150 64 column23_tail (by decide) i)
#print axioms column23_tail
#print axioms column23_lower

theorem column26_tail : orderedRows.drop 153 = SourceBlockSupport.column26_later := by decide
theorem column26_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 61) :
    orderedMinor half alpha a b c ⟨153+i.val, by omega⟩ 150 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (153+i.val) 0) 95 = 0
  unfold entry
  simp only [show 4*(22+95/3) = 212 from rfl,
    show 1+95%3 = 3 from rfl, show 212+3 = 215 from rfl]
  exact SourceBlockSupport.column26_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 153 61 column26_tail (by decide) i)
#print axioms column26_tail
#print axioms column26_lower

theorem column27_tail : orderedRows.drop 153 = SourceBlockSupport.column27_later := by decide
theorem column27_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 61) :
    orderedMinor half alpha a b c ⟨153+i.val, by omega⟩ 151 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (153+i.val) 0) 96 = 0
  unfold entry
  simp only [show 4*(22+96/3) = 216 from rfl,
    show 1+96%3 = 1 from rfl, show 216+1 = 217 from rfl]
  exact SourceBlockSupport.column27_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 153 61 column27_tail (by decide) i)
#print axioms column27_tail
#print axioms column27_lower

end AspisV8R17.SourceMinor.LowerBlocks
