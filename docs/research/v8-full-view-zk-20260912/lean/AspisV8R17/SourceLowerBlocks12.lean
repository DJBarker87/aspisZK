import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport12

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column175_tail : orderedRows.drop 98 = SourceBlockSupport.column175_later := by decide
theorem column175_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 116) :
    orderedMinor half alpha a b c ⟨98+i.val, by omega⟩ 96 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (98+i.val) 0) 641 = 0
  unfold entry
  simp only [show 4*(22+641/3) = 940 from rfl,
    show 1+641%3 = 3 from rfl, show 940+3 = 943 from rfl]
  exact SourceBlockSupport.column175_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 98 116 column175_tail (by decide) i)
#print axioms column175_tail
#print axioms column175_lower

theorem column176_tail : orderedRows.drop 98 = SourceBlockSupport.column176_later := by decide
theorem column176_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 116) :
    orderedMinor half alpha a b c ⟨98+i.val, by omega⟩ 97 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (98+i.val) 0) 642 = 0
  unfold entry
  simp only [show 4*(22+642/3) = 944 from rfl,
    show 1+642%3 = 1 from rfl, show 944+1 = 945 from rfl]
  exact SourceBlockSupport.column176_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 98 116 column176_tail (by decide) i)
#print axioms column176_tail
#print axioms column176_lower

theorem column177_tail : orderedRows.drop 100 = SourceBlockSupport.column177_later := by decide
theorem column177_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 114) :
    orderedMinor half alpha a b c ⟨100+i.val, by omega⟩ 98 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (100+i.val) 0) 644 = 0
  unfold entry
  simp only [show 4*(22+644/3) = 944 from rfl,
    show 1+644%3 = 3 from rfl, show 944+3 = 947 from rfl]
  exact SourceBlockSupport.column177_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 100 114 column177_tail (by decide) i)
#print axioms column177_tail
#print axioms column177_lower

theorem column178_tail : orderedRows.drop 100 = SourceBlockSupport.column178_later := by decide
theorem column178_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 114) :
    orderedMinor half alpha a b c ⟨100+i.val, by omega⟩ 99 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (100+i.val) 0) 645 = 0
  unfold entry
  simp only [show 4*(22+645/3) = 948 from rfl,
    show 1+645%3 = 1 from rfl, show 948+1 = 949 from rfl]
  exact SourceBlockSupport.column178_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 100 114 column178_tail (by decide) i)
#print axioms column178_tail
#print axioms column178_lower

theorem column179_tail : orderedRows.drop 102 = SourceBlockSupport.column179_later := by decide
theorem column179_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 112) :
    orderedMinor half alpha a b c ⟨102+i.val, by omega⟩ 100 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (102+i.val) 0) 647 = 0
  unfold entry
  simp only [show 4*(22+647/3) = 948 from rfl,
    show 1+647%3 = 3 from rfl, show 948+3 = 951 from rfl]
  exact SourceBlockSupport.column179_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 102 112 column179_tail (by decide) i)
#print axioms column179_tail
#print axioms column179_lower

theorem column180_tail : orderedRows.drop 102 = SourceBlockSupport.column180_later := by decide
theorem column180_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 112) :
    orderedMinor half alpha a b c ⟨102+i.val, by omega⟩ 101 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (102+i.val) 0) 648 = 0
  unfold entry
  simp only [show 4*(22+648/3) = 952 from rfl,
    show 1+648%3 = 1 from rfl, show 952+1 = 953 from rfl]
  exact SourceBlockSupport.column180_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 102 112 column180_tail (by decide) i)
#print axioms column180_tail
#print axioms column180_lower

theorem column181_tail : orderedRows.drop 104 = SourceBlockSupport.column181_later := by decide
theorem column181_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 110) :
    orderedMinor half alpha a b c ⟨104+i.val, by omega⟩ 102 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (104+i.val) 0) 650 = 0
  unfold entry
  simp only [show 4*(22+650/3) = 952 from rfl,
    show 1+650%3 = 3 from rfl, show 952+3 = 955 from rfl]
  exact SourceBlockSupport.column181_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 104 110 column181_tail (by decide) i)
#print axioms column181_tail
#print axioms column181_lower

theorem column182_tail : orderedRows.drop 104 = SourceBlockSupport.column182_later := by decide
theorem column182_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 110) :
    orderedMinor half alpha a b c ⟨104+i.val, by omega⟩ 103 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (104+i.val) 0) 651 = 0
  unfold entry
  simp only [show 4*(22+651/3) = 956 from rfl,
    show 1+651%3 = 1 from rfl, show 956+1 = 957 from rfl]
  exact SourceBlockSupport.column182_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 104 110 column182_tail (by decide) i)
#print axioms column182_tail
#print axioms column182_lower

end AspisV8R17.SourceMinor.LowerBlocks
