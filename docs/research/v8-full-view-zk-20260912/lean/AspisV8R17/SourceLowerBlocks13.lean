import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport13

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column183_tail : orderedRows.drop 106 = SourceBlockSupport.column183_later := by decide
theorem column183_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 108) :
    orderedMinor half alpha a b c ⟨106+i.val, by omega⟩ 104 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (106+i.val) 0) 653 = 0
  unfold entry
  simp only [show 4*(22+653/3) = 956 from rfl,
    show 1+653%3 = 3 from rfl, show 956+3 = 959 from rfl]
  exact SourceBlockSupport.column183_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 106 108 column183_tail (by decide) i)
#print axioms column183_tail
#print axioms column183_lower

theorem column184_tail : orderedRows.drop 106 = SourceBlockSupport.column184_later := by decide
theorem column184_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 108) :
    orderedMinor half alpha a b c ⟨106+i.val, by omega⟩ 105 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (106+i.val) 0) 654 = 0
  unfold entry
  simp only [show 4*(22+654/3) = 960 from rfl,
    show 1+654%3 = 1 from rfl, show 960+1 = 961 from rfl]
  exact SourceBlockSupport.column184_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 106 108 column184_tail (by decide) i)
#print axioms column184_tail
#print axioms column184_lower

theorem column185_tail : orderedRows.drop 108 = SourceBlockSupport.column185_later := by decide
theorem column185_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 106) :
    orderedMinor half alpha a b c ⟨108+i.val, by omega⟩ 106 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (108+i.val) 0) 656 = 0
  unfold entry
  simp only [show 4*(22+656/3) = 960 from rfl,
    show 1+656%3 = 3 from rfl, show 960+3 = 963 from rfl]
  exact SourceBlockSupport.column185_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 108 106 column185_tail (by decide) i)
#print axioms column185_tail
#print axioms column185_lower

theorem column186_tail : orderedRows.drop 108 = SourceBlockSupport.column186_later := by decide
theorem column186_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 106) :
    orderedMinor half alpha a b c ⟨108+i.val, by omega⟩ 107 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (108+i.val) 0) 657 = 0
  unfold entry
  simp only [show 4*(22+657/3) = 964 from rfl,
    show 1+657%3 = 1 from rfl, show 964+1 = 965 from rfl]
  exact SourceBlockSupport.column186_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 108 106 column186_tail (by decide) i)
#print axioms column186_tail
#print axioms column186_lower

theorem column187_tail : orderedRows.drop 110 = SourceBlockSupport.column187_later := by decide
theorem column187_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 104) :
    orderedMinor half alpha a b c ⟨110+i.val, by omega⟩ 108 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (110+i.val) 0) 659 = 0
  unfold entry
  simp only [show 4*(22+659/3) = 964 from rfl,
    show 1+659%3 = 3 from rfl, show 964+3 = 967 from rfl]
  exact SourceBlockSupport.column187_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 110 104 column187_tail (by decide) i)
#print axioms column187_tail
#print axioms column187_lower

theorem column188_tail : orderedRows.drop 110 = SourceBlockSupport.column188_later := by decide
theorem column188_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 104) :
    orderedMinor half alpha a b c ⟨110+i.val, by omega⟩ 109 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (110+i.val) 0) 660 = 0
  unfold entry
  simp only [show 4*(22+660/3) = 968 from rfl,
    show 1+660%3 = 1 from rfl, show 968+1 = 969 from rfl]
  exact SourceBlockSupport.column188_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 110 104 column188_tail (by decide) i)
#print axioms column188_tail
#print axioms column188_lower

theorem column189_tail : orderedRows.drop 112 = SourceBlockSupport.column189_later := by decide
theorem column189_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 102) :
    orderedMinor half alpha a b c ⟨112+i.val, by omega⟩ 110 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (112+i.val) 0) 662 = 0
  unfold entry
  simp only [show 4*(22+662/3) = 968 from rfl,
    show 1+662%3 = 3 from rfl, show 968+3 = 971 from rfl]
  exact SourceBlockSupport.column189_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 112 102 column189_tail (by decide) i)
#print axioms column189_tail
#print axioms column189_lower

theorem column190_tail : orderedRows.drop 112 = SourceBlockSupport.column190_later := by decide
theorem column190_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 102) :
    orderedMinor half alpha a b c ⟨112+i.val, by omega⟩ 111 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (112+i.val) 0) 663 = 0
  unfold entry
  simp only [show 4*(22+663/3) = 972 from rfl,
    show 1+663%3 = 1 from rfl, show 972+1 = 973 from rfl]
  exact SourceBlockSupport.column190_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 112 102 column190_tail (by decide) i)
#print axioms column190_tail
#print axioms column190_lower

end AspisV8R17.SourceMinor.LowerBlocks
