import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport09

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column146_tail : orderedRows.drop 73 = SourceBlockSupport.column146_later := by decide
theorem column146_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 141) :
    orderedMinor half alpha a b c ⟨73+i.val, by omega⟩ 72 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (73+i.val) 0) 555 = 0
  unfold entry
  simp only [show 4*(22+555/3) = 828 from rfl,
    show 1+555%3 = 1 from rfl, show 828+1 = 829 from rfl]
  exact SourceBlockSupport.column146_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 73 141 column146_tail (by decide) i)
#print axioms column146_tail
#print axioms column146_lower

theorem column149_tail : orderedRows.drop 74 = SourceBlockSupport.column149_later := by decide
theorem column149_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 140) :
    orderedMinor half alpha a b c ⟨74+i.val, by omega⟩ 73 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (74+i.val) 0) 567 = 0
  unfold entry
  simp only [show 4*(22+567/3) = 844 from rfl,
    show 1+567%3 = 1 from rfl, show 844+1 = 845 from rfl]
  exact SourceBlockSupport.column149_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 74 140 column149_tail (by decide) i)
#print axioms column149_tail
#print axioms column149_lower

theorem column150_tail : orderedRows.drop 75 = SourceBlockSupport.column150_later := by decide
theorem column150_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 139) :
    orderedMinor half alpha a b c ⟨75+i.val, by omega⟩ 74 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (75+i.val) 0) 576 = 0
  unfold entry
  simp only [show 4*(22+576/3) = 856 from rfl,
    show 1+576%3 = 1 from rfl, show 856+1 = 857 from rfl]
  exact SourceBlockSupport.column150_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 75 139 column150_tail (by decide) i)
#print axioms column150_tail
#print axioms column150_lower

theorem column152_tail : orderedRows.drop 77 = SourceBlockSupport.column152_later := by decide
theorem column152_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 137) :
    orderedMinor half alpha a b c ⟨77+i.val, by omega⟩ 75 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (77+i.val) 0) 588 = 0
  unfold entry
  simp only [show 4*(22+588/3) = 872 from rfl,
    show 1+588%3 = 1 from rfl, show 872+1 = 873 from rfl]
  exact SourceBlockSupport.column152_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 77 137 column152_tail (by decide) i)
#print axioms column152_tail
#print axioms column152_lower

theorem column153_tail : orderedRows.drop 77 = SourceBlockSupport.column153_later := by decide
theorem column153_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 137) :
    orderedMinor half alpha a b c ⟨77+i.val, by omega⟩ 76 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (77+i.val) 0) 589 = 0
  unfold entry
  simp only [show 4*(22+589/3) = 872 from rfl,
    show 1+589%3 = 2 from rfl, show 872+2 = 874 from rfl]
  exact SourceBlockSupport.column153_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 77 137 column153_tail (by decide) i)
#print axioms column153_tail
#print axioms column153_lower

theorem column161_tail : orderedRows.drop 79 = SourceBlockSupport.column161_later := by decide
theorem column161_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 135) :
    orderedMinor half alpha a b c ⟨79+i.val, by omega⟩ 77 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (79+i.val) 0) 620 = 0
  unfold entry
  simp only [show 4*(22+620/3) = 912 from rfl,
    show 1+620%3 = 3 from rfl, show 912+3 = 915 from rfl]
  exact SourceBlockSupport.column161_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 79 135 column161_tail (by decide) i)
#print axioms column161_tail
#print axioms column161_lower

theorem column162_tail : orderedRows.drop 79 = SourceBlockSupport.column162_later := by decide
theorem column162_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 135) :
    orderedMinor half alpha a b c ⟨79+i.val, by omega⟩ 78 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (79+i.val) 0) 621 = 0
  unfold entry
  simp only [show 4*(22+621/3) = 916 from rfl,
    show 1+621%3 = 1 from rfl, show 916+1 = 917 from rfl]
  exact SourceBlockSupport.column162_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 79 135 column162_tail (by decide) i)
#print axioms column162_tail
#print axioms column162_lower

theorem column151_tail : orderedRows.drop 80 = SourceBlockSupport.column151_later := by decide
theorem column151_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 134) :
    orderedMinor half alpha a b c ⟨80+i.val, by omega⟩ 79 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (80+i.val) 0) 579 = 0
  unfold entry
  simp only [show 4*(22+579/3) = 860 from rfl,
    show 1+579%3 = 1 from rfl, show 860+1 = 861 from rfl]
  exact SourceBlockSupport.column151_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 80 134 column151_tail (by decide) i)
#print axioms column151_tail
#print axioms column151_lower

end AspisV8R17.SourceMinor.LowerBlocks
