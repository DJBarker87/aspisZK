import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport22

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column211_tail : orderedRows.drop 177 = SourceBlockSupport.column211_later := by decide
theorem column211_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 37) :
    orderedMinor half alpha a b c ⟨177+i.val, by omega⟩ 176 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (177+i.val) 0) 693 = 0
  unfold entry
  simp only [show 4*(22+693/3) = 1012 from rfl,
    show 1+693%3 = 1 from rfl, show 1012+1 = 1013 from rfl]
  exact SourceBlockSupport.column211_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 177 37 column211_tail (by decide) i)
#print axioms column211_tail
#print axioms column211_lower

theorem column12_tail : orderedRows.drop 179 = SourceBlockSupport.column12_later := by decide
theorem column12_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 35) :
    orderedMinor half alpha a b c ⟨179+i.val, by omega⟩ 177 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (179+i.val) 0) 47 = 0
  unfold entry
  simp only [show 4*(22+47/3) = 148 from rfl,
    show 1+47%3 = 3 from rfl, show 148+3 = 151 from rfl]
  exact SourceBlockSupport.column12_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 179 35 column12_tail (by decide) i)
#print axioms column12_tail
#print axioms column12_lower

theorem column13_tail : orderedRows.drop 179 = SourceBlockSupport.column13_later := by decide
theorem column13_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 35) :
    orderedMinor half alpha a b c ⟨179+i.val, by omega⟩ 178 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (179+i.val) 0) 48 = 0
  unfold entry
  simp only [show 4*(22+48/3) = 152 from rfl,
    show 1+48%3 = 1 from rfl, show 152+1 = 153 from rfl]
  exact SourceBlockSupport.column13_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 179 35 column13_tail (by decide) i)
#print axioms column13_tail
#print axioms column13_lower

theorem column18_tail : orderedRows.drop 181 = SourceBlockSupport.column18_later := by decide
theorem column18_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 33) :
    orderedMinor half alpha a b c ⟨181+i.val, by omega⟩ 179 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (181+i.val) 0) 66 = 0
  unfold entry
  simp only [show 4*(22+66/3) = 176 from rfl,
    show 1+66%3 = 1 from rfl, show 176+1 = 177 from rfl]
  exact SourceBlockSupport.column18_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 181 33 column18_tail (by decide) i)
#print axioms column18_tail
#print axioms column18_lower

theorem column19_tail : orderedRows.drop 181 = SourceBlockSupport.column19_later := by decide
theorem column19_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 33) :
    orderedMinor half alpha a b c ⟨181+i.val, by omega⟩ 180 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (181+i.val) 0) 67 = 0
  unfold entry
  simp only [show 4*(22+67/3) = 176 from rfl,
    show 1+67%3 = 2 from rfl, show 176+2 = 178 from rfl]
  exact SourceBlockSupport.column19_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 181 33 column19_tail (by decide) i)
#print axioms column19_tail
#print axioms column19_lower

theorem column24_tail : orderedRows.drop 183 = SourceBlockSupport.column24_later := by decide
theorem column24_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 31) :
    orderedMinor half alpha a b c ⟨183+i.val, by omega⟩ 181 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (183+i.val) 0) 86 = 0
  unfold entry
  simp only [show 4*(22+86/3) = 200 from rfl,
    show 1+86%3 = 3 from rfl, show 200+3 = 203 from rfl]
  exact SourceBlockSupport.column24_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 183 31 column24_tail (by decide) i)
#print axioms column24_tail
#print axioms column24_lower

theorem column25_tail : orderedRows.drop 183 = SourceBlockSupport.column25_later := by decide
theorem column25_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 31) :
    orderedMinor half alpha a b c ⟨183+i.val, by omega⟩ 182 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (183+i.val) 0) 87 = 0
  unfold entry
  simp only [show 4*(22+87/3) = 204 from rfl,
    show 1+87%3 = 1 from rfl, show 204+1 = 205 from rfl]
  exact SourceBlockSupport.column25_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 183 31 column25_tail (by decide) i)
#print axioms column25_tail
#print axioms column25_lower

theorem column30_tail : orderedRows.drop 185 = SourceBlockSupport.column30_later := by decide
theorem column30_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 29) :
    orderedMinor half alpha a b c ⟨185+i.val, by omega⟩ 183 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (185+i.val) 0) 105 = 0
  unfold entry
  simp only [show 4*(22+105/3) = 228 from rfl,
    show 1+105%3 = 1 from rfl, show 228+1 = 229 from rfl]
  exact SourceBlockSupport.column30_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 185 29 column30_tail (by decide) i)
#print axioms column30_tail
#print axioms column30_lower

end AspisV8R17.SourceMinor.LowerBlocks
