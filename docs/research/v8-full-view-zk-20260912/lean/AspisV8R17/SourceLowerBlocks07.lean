import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport07

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column136_tail : orderedRows.drop 57 = SourceBlockSupport.column136_later := by decide
theorem column136_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 157) :
    orderedMinor half alpha a b c ⟨57+i.val, by omega⟩ 56 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (57+i.val) 0) 517 = 0
  unfold entry
  simp only [show 4*(22+517/3) = 776 from rfl,
    show 1+517%3 = 2 from rfl, show 776+2 = 778 from rfl]
  exact SourceBlockSupport.column136_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 57 157 column136_tail (by decide) i)
#print axioms column136_tail
#print axioms column136_lower

theorem column134_tail : orderedRows.drop 58 = SourceBlockSupport.column134_later := by decide
theorem column134_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 156) :
    orderedMinor half alpha a b c ⟨58+i.val, by omega⟩ 57 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (58+i.val) 0) 507 = 0
  unfold entry
  simp only [show 4*(22+507/3) = 764 from rfl,
    show 1+507%3 = 1 from rfl, show 764+1 = 765 from rfl]
  exact SourceBlockSupport.column134_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 58 156 column134_tail (by decide) i)
#print axioms column134_tail
#print axioms column134_lower

theorem column138_tail : orderedRows.drop 60 = SourceBlockSupport.column138_later := by decide
theorem column138_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 154) :
    orderedMinor half alpha a b c ⟨60+i.val, by omega⟩ 58 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (60+i.val) 0) 528 = 0
  unfold entry
  simp only [show 4*(22+528/3) = 792 from rfl,
    show 1+528%3 = 1 from rfl, show 792+1 = 793 from rfl]
  exact SourceBlockSupport.column138_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 60 154 column138_tail (by decide) i)
#print axioms column138_tail
#print axioms column138_lower

theorem column139_tail : orderedRows.drop 60 = SourceBlockSupport.column139_later := by decide
theorem column139_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 154) :
    orderedMinor half alpha a b c ⟨60+i.val, by omega⟩ 59 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (60+i.val) 0) 529 = 0
  unfold entry
  simp only [show 4*(22+529/3) = 792 from rfl,
    show 1+529%3 = 2 from rfl, show 792+2 = 794 from rfl]
  exact SourceBlockSupport.column139_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 60 154 column139_tail (by decide) i)
#print axioms column139_tail
#print axioms column139_lower

theorem column137_tail : orderedRows.drop 61 = SourceBlockSupport.column137_later := by decide
theorem column137_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 153) :
    orderedMinor half alpha a b c ⟨61+i.val, by omega⟩ 60 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (61+i.val) 0) 519 = 0
  unfold entry
  simp only [show 4*(22+519/3) = 780 from rfl,
    show 1+519%3 = 1 from rfl, show 780+1 = 781 from rfl]
  exact SourceBlockSupport.column137_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 61 153 column137_tail (by decide) i)
#print axioms column137_tail
#print axioms column137_lower

theorem column141_tail : orderedRows.drop 63 = SourceBlockSupport.column141_later := by decide
theorem column141_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 151) :
    orderedMinor half alpha a b c ⟨63+i.val, by omega⟩ 61 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (63+i.val) 0) 540 = 0
  unfold entry
  simp only [show 4*(22+540/3) = 808 from rfl,
    show 1+540%3 = 1 from rfl, show 808+1 = 809 from rfl]
  exact SourceBlockSupport.column141_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 63 151 column141_tail (by decide) i)
#print axioms column141_tail
#print axioms column141_lower

theorem column142_tail : orderedRows.drop 63 = SourceBlockSupport.column142_later := by decide
theorem column142_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 151) :
    orderedMinor half alpha a b c ⟨63+i.val, by omega⟩ 62 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (63+i.val) 0) 541 = 0
  unfold entry
  simp only [show 4*(22+541/3) = 808 from rfl,
    show 1+541%3 = 2 from rfl, show 808+2 = 810 from rfl]
  exact SourceBlockSupport.column142_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 63 151 column142_tail (by decide) i)
#print axioms column142_tail
#print axioms column142_lower

theorem column140_tail : orderedRows.drop 64 = SourceBlockSupport.column140_later := by decide
theorem column140_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 150) :
    orderedMinor half alpha a b c ⟨64+i.val, by omega⟩ 63 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (64+i.val) 0) 531 = 0
  unfold entry
  simp only [show 4*(22+531/3) = 796 from rfl,
    show 1+531%3 = 1 from rfl, show 796+1 = 797 from rfl]
  exact SourceBlockSupport.column140_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 64 150 column140_tail (by decide) i)
#print axioms column140_tail
#print axioms column140_lower

end AspisV8R17.SourceMinor.LowerBlocks
