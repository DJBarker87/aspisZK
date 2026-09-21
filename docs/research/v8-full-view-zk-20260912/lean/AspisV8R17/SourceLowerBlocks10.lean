import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport10

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column155_tail : orderedRows.drop 82 = SourceBlockSupport.column155_later := by decide
theorem column155_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 132) :
    orderedMinor half alpha a b c ⟨82+i.val, by omega⟩ 80 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (82+i.val) 0) 600 = 0
  unfold entry
  simp only [show 4*(22+600/3) = 888 from rfl,
    show 1+600%3 = 1 from rfl, show 888+1 = 889 from rfl]
  exact SourceBlockSupport.column155_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 82 132 column155_tail (by decide) i)
#print axioms column155_tail
#print axioms column155_lower

theorem column156_tail : orderedRows.drop 82 = SourceBlockSupport.column156_later := by decide
theorem column156_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 132) :
    orderedMinor half alpha a b c ⟨82+i.val, by omega⟩ 81 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (82+i.val) 0) 601 = 0
  unfold entry
  simp only [show 4*(22+601/3) = 888 from rfl,
    show 1+601%3 = 2 from rfl, show 888+2 = 890 from rfl]
  exact SourceBlockSupport.column156_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 82 132 column156_tail (by decide) i)
#print axioms column156_tail
#print axioms column156_lower

theorem column154_tail : orderedRows.drop 83 = SourceBlockSupport.column154_later := by decide
theorem column154_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 131) :
    orderedMinor half alpha a b c ⟨83+i.val, by omega⟩ 82 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (83+i.val) 0) 591 = 0
  unfold entry
  simp only [show 4*(22+591/3) = 876 from rfl,
    show 1+591%3 = 1 from rfl, show 876+1 = 877 from rfl]
  exact SourceBlockSupport.column154_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 83 131 column154_tail (by decide) i)
#print axioms column154_tail
#print axioms column154_lower

theorem column163_tail : orderedRows.drop 85 = SourceBlockSupport.column163_later := by decide
theorem column163_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 129) :
    orderedMinor half alpha a b c ⟨85+i.val, by omega⟩ 83 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (85+i.val) 0) 623 = 0
  unfold entry
  simp only [show 4*(22+623/3) = 916 from rfl,
    show 1+623%3 = 3 from rfl, show 916+3 = 919 from rfl]
  exact SourceBlockSupport.column163_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 85 129 column163_tail (by decide) i)
#print axioms column163_tail
#print axioms column163_lower

theorem column164_tail : orderedRows.drop 85 = SourceBlockSupport.column164_later := by decide
theorem column164_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 129) :
    orderedMinor half alpha a b c ⟨85+i.val, by omega⟩ 84 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (85+i.val) 0) 624 = 0
  unfold entry
  simp only [show 4*(22+624/3) = 920 from rfl,
    show 1+624%3 = 1 from rfl, show 920+1 = 921 from rfl]
  exact SourceBlockSupport.column164_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 85 129 column164_tail (by decide) i)
#print axioms column164_tail
#print axioms column164_lower

theorem column157_tail : orderedRows.drop 86 = SourceBlockSupport.column157_later := by decide
theorem column157_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 128) :
    orderedMinor half alpha a b c ⟨86+i.val, by omega⟩ 85 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (86+i.val) 0) 603 = 0
  unfold entry
  simp only [show 4*(22+603/3) = 892 from rfl,
    show 1+603%3 = 1 from rfl, show 892+1 = 893 from rfl]
  exact SourceBlockSupport.column157_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 86 128 column157_tail (by decide) i)
#print axioms column157_tail
#print axioms column157_lower

theorem column165_tail : orderedRows.drop 88 = SourceBlockSupport.column165_later := by decide
theorem column165_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 126) :
    orderedMinor half alpha a b c ⟨88+i.val, by omega⟩ 86 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (88+i.val) 0) 626 = 0
  unfold entry
  simp only [show 4*(22+626/3) = 920 from rfl,
    show 1+626%3 = 3 from rfl, show 920+3 = 923 from rfl]
  exact SourceBlockSupport.column165_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 88 126 column165_tail (by decide) i)
#print axioms column165_tail
#print axioms column165_lower

theorem column166_tail : orderedRows.drop 88 = SourceBlockSupport.column166_later := by decide
theorem column166_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 126) :
    orderedMinor half alpha a b c ⟨88+i.val, by omega⟩ 87 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (88+i.val) 0) 627 = 0
  unfold entry
  simp only [show 4*(22+627/3) = 924 from rfl,
    show 1+627%3 = 1 from rfl, show 924+1 = 925 from rfl]
  exact SourceBlockSupport.column166_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 88 126 column166_tail (by decide) i)
#print axioms column166_tail
#print axioms column166_lower

end AspisV8R17.SourceMinor.LowerBlocks
