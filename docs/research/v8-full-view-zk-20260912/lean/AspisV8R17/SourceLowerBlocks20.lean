import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport20

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column44_tail : orderedRows.drop 162 = SourceBlockSupport.column44_later := by decide
theorem column44_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 52) :
    orderedMinor half alpha a b c ⟨162+i.val, by omega⟩ 160 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (162+i.val) 0) 153 = 0
  unfold entry
  simp only [show 4*(22+153/3) = 292 from rfl,
    show 1+153%3 = 1 from rfl, show 292+1 = 293 from rfl]
  exact SourceBlockSupport.column44_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 162 52 column44_tail (by decide) i)
#print axioms column44_tail
#print axioms column44_lower

theorem column45_tail : orderedRows.drop 162 = SourceBlockSupport.column45_later := by decide
theorem column45_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 52) :
    orderedMinor half alpha a b c ⟨162+i.val, by omega⟩ 161 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (162+i.val) 0) 154 = 0
  unfold entry
  simp only [show 4*(22+154/3) = 292 from rfl,
    show 1+154%3 = 2 from rfl, show 292+2 = 294 from rfl]
  exact SourceBlockSupport.column45_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 162 52 column45_tail (by decide) i)
#print axioms column45_tail
#print axioms column45_lower

theorem column47_tail : orderedRows.drop 163 = SourceBlockSupport.column47_later := by decide
theorem column47_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 51) :
    orderedMinor half alpha a b c ⟨163+i.val, by omega⟩ 162 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (163+i.val) 0) 162 = 0
  unfold entry
  simp only [show 4*(22+162/3) = 304 from rfl,
    show 1+162%3 = 1 from rfl, show 304+1 = 305 from rfl]
  exact SourceBlockSupport.column47_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 163 51 column47_tail (by decide) i)
#print axioms column47_tail
#print axioms column47_lower

theorem column53_tail : orderedRows.drop 164 = SourceBlockSupport.column53_later := by decide
theorem column53_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 50) :
    orderedMinor half alpha a b c ⟨164+i.val, by omega⟩ 163 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (164+i.val) 0) 182 = 0
  unfold entry
  simp only [show 4*(22+182/3) = 328 from rfl,
    show 1+182%3 = 3 from rfl, show 328+3 = 331 from rfl]
  exact SourceBlockSupport.column53_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 164 50 column53_tail (by decide) i)
#print axioms column53_tail
#print axioms column53_lower

theorem column56_tail : orderedRows.drop 166 = SourceBlockSupport.column56_later := by decide
theorem column56_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 48) :
    orderedMinor half alpha a b c ⟨166+i.val, by omega⟩ 164 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (166+i.val) 0) 192 = 0
  unfold entry
  simp only [show 4*(22+192/3) = 344 from rfl,
    show 1+192%3 = 1 from rfl, show 344+1 = 345 from rfl]
  exact SourceBlockSupport.column56_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 166 48 column56_tail (by decide) i)
#print axioms column56_tail
#print axioms column56_lower

theorem column57_tail : orderedRows.drop 166 = SourceBlockSupport.column57_later := by decide
theorem column57_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 48) :
    orderedMinor half alpha a b c ⟨166+i.val, by omega⟩ 165 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (166+i.val) 0) 193 = 0
  unfold entry
  simp only [show 4*(22+193/3) = 344 from rfl,
    show 1+193%3 = 2 from rfl, show 344+2 = 346 from rfl]
  exact SourceBlockSupport.column57_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 166 48 column57_tail (by decide) i)
#print axioms column57_tail
#print axioms column57_lower

theorem column59_tail : orderedRows.drop 167 = SourceBlockSupport.column59_later := by decide
theorem column59_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 47) :
    orderedMinor half alpha a b c ⟨167+i.val, by omega⟩ 166 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (167+i.val) 0) 201 = 0
  unfold entry
  simp only [show 4*(22+201/3) = 356 from rfl,
    show 1+201%3 = 1 from rfl, show 356+1 = 357 from rfl]
  exact SourceBlockSupport.column59_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 167 47 column59_tail (by decide) i)
#print axioms column59_tail
#print axioms column59_lower

theorem column62_tail : orderedRows.drop 170 = SourceBlockSupport.column62_later := by decide
theorem column62_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 44) :
    orderedMinor half alpha a b c ⟨170+i.val, by omega⟩ 167 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (170+i.val) 0) 212 = 0
  unfold entry
  simp only [show 4*(22+212/3) = 368 from rfl,
    show 1+212%3 = 3 from rfl, show 368+3 = 371 from rfl]
  exact SourceBlockSupport.column62_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 170 44 column62_tail (by decide) i)
#print axioms column62_tail
#print axioms column62_lower

end AspisV8R17.SourceMinor.LowerBlocks
