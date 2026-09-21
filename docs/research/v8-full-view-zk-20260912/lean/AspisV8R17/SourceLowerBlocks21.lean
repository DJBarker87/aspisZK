import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport21

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column63_tail : orderedRows.drop 170 = SourceBlockSupport.column63_later := by decide
theorem column63_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 44) :
    orderedMinor half alpha a b c ⟨170+i.val, by omega⟩ 168 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (170+i.val) 0) 213 = 0
  unfold entry
  simp only [show 4*(22+213/3) = 372 from rfl,
    show 1+213%3 = 1 from rfl, show 372+1 = 373 from rfl]
  exact SourceBlockSupport.column63_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 170 44 column63_tail (by decide) i)
#print axioms column63_tail
#print axioms column63_lower

theorem column64_tail : orderedRows.drop 170 = SourceBlockSupport.column64_later := by decide
theorem column64_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 44) :
    orderedMinor half alpha a b c ⟨170+i.val, by omega⟩ 169 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (170+i.val) 0) 214 = 0
  unfold entry
  simp only [show 4*(22+214/3) = 372 from rfl,
    show 1+214%3 = 2 from rfl, show 372+2 = 374 from rfl]
  exact SourceBlockSupport.column64_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 170 44 column64_tail (by decide) i)
#print axioms column64_tail
#print axioms column64_lower

theorem column68_tail : orderedRows.drop 172 = SourceBlockSupport.column68_later := by decide
theorem column68_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 42) :
    orderedMinor half alpha a b c ⟨172+i.val, by omega⟩ 170 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (172+i.val) 0) 231 = 0
  unfold entry
  simp only [show 4*(22+231/3) = 396 from rfl,
    show 1+231%3 = 1 from rfl, show 396+1 = 397 from rfl]
  exact SourceBlockSupport.column68_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 172 42 column68_tail (by decide) i)
#print axioms column68_tail
#print axioms column68_lower

theorem column69_tail : orderedRows.drop 172 = SourceBlockSupport.column69_later := by decide
theorem column69_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 42) :
    orderedMinor half alpha a b c ⟨172+i.val, by omega⟩ 171 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (172+i.val) 0) 232 = 0
  unfold entry
  simp only [show 4*(22+232/3) = 396 from rfl,
    show 1+232%3 = 2 from rfl, show 396+2 = 398 from rfl]
  exact SourceBlockSupport.column69_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 172 42 column69_tail (by decide) i)
#print axioms column69_tail
#print axioms column69_lower

theorem column73_tail : orderedRows.drop 175 = SourceBlockSupport.column73_later := by decide
theorem column73_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 39) :
    orderedMinor half alpha a b c ⟨175+i.val, by omega⟩ 172 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (175+i.val) 0) 251 = 0
  unfold entry
  simp only [show 4*(22+251/3) = 420 from rfl,
    show 1+251%3 = 3 from rfl, show 420+3 = 423 from rfl]
  exact SourceBlockSupport.column73_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 175 39 column73_tail (by decide) i)
#print axioms column73_tail
#print axioms column73_lower

theorem column74_tail : orderedRows.drop 175 = SourceBlockSupport.column74_later := by decide
theorem column74_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 39) :
    orderedMinor half alpha a b c ⟨175+i.val, by omega⟩ 173 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (175+i.val) 0) 252 = 0
  unfold entry
  simp only [show 4*(22+252/3) = 424 from rfl,
    show 1+252%3 = 1 from rfl, show 424+1 = 425 from rfl]
  exact SourceBlockSupport.column74_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 175 39 column74_tail (by decide) i)
#print axioms column74_tail
#print axioms column74_lower

theorem column75_tail : orderedRows.drop 175 = SourceBlockSupport.column75_later := by decide
theorem column75_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 39) :
    orderedMinor half alpha a b c ⟨175+i.val, by omega⟩ 174 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (175+i.val) 0) 253 = 0
  unfold entry
  simp only [show 4*(22+253/3) = 424 from rfl,
    show 1+253%3 = 2 from rfl, show 424+2 = 426 from rfl]
  exact SourceBlockSupport.column75_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 175 39 column75_tail (by decide) i)
#print axioms column75_tail
#print axioms column75_lower

theorem column79_tail : orderedRows.drop 176 = SourceBlockSupport.column79_later := by decide
theorem column79_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 38) :
    orderedMinor half alpha a b c ⟨176+i.val, by omega⟩ 175 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (176+i.val) 0) 279 = 0
  unfold entry
  simp only [show 4*(22+279/3) = 460 from rfl,
    show 1+279%3 = 1 from rfl, show 460+1 = 461 from rfl]
  exact SourceBlockSupport.column79_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 176 38 column79_tail (by decide) i)
#print axioms column79_tail
#print axioms column79_lower

end AspisV8R17.SourceMinor.LowerBlocks
