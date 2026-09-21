import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport08

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column144_tail : orderedRows.drop 66 = SourceBlockSupport.column144_later := by decide
theorem column144_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 148) :
    orderedMinor half alpha a b c ⟨66+i.val, by omega⟩ 64 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (66+i.val) 0) 552 = 0
  unfold entry
  simp only [show 4*(22+552/3) = 824 from rfl,
    show 1+552%3 = 1 from rfl, show 824+1 = 825 from rfl]
  exact SourceBlockSupport.column144_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 66 148 column144_tail (by decide) i)
#print axioms column144_tail
#print axioms column144_lower

theorem column145_tail : orderedRows.drop 66 = SourceBlockSupport.column145_later := by decide
theorem column145_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 148) :
    orderedMinor half alpha a b c ⟨66+i.val, by omega⟩ 65 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (66+i.val) 0) 553 = 0
  unfold entry
  simp only [show 4*(22+553/3) = 824 from rfl,
    show 1+553%3 = 2 from rfl, show 824+2 = 826 from rfl]
  exact SourceBlockSupport.column145_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 66 148 column145_tail (by decide) i)
#print axioms column145_tail
#print axioms column145_lower

theorem column158_tail : orderedRows.drop 67 = SourceBlockSupport.column158_later := by decide
theorem column158_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 147) :
    orderedMinor half alpha a b c ⟨67+i.val, by omega⟩ 66 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (67+i.val) 0) 612 = 0
  unfold entry
  simp only [show 4*(22+612/3) = 904 from rfl,
    show 1+612%3 = 1 from rfl, show 904+1 = 905 from rfl]
  exact SourceBlockSupport.column158_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 67 147 column158_tail (by decide) i)
#print axioms column158_tail
#print axioms column158_lower

theorem column143_tail : orderedRows.drop 68 = SourceBlockSupport.column143_later := by decide
theorem column143_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 146) :
    orderedMinor half alpha a b c ⟨68+i.val, by omega⟩ 67 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (68+i.val) 0) 543 = 0
  unfold entry
  simp only [show 4*(22+543/3) = 812 from rfl,
    show 1+543%3 = 1 from rfl, show 812+1 = 813 from rfl]
  exact SourceBlockSupport.column143_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 68 146 column143_tail (by decide) i)
#print axioms column143_tail
#print axioms column143_lower

theorem column147_tail : orderedRows.drop 70 = SourceBlockSupport.column147_later := by decide
theorem column147_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 144) :
    orderedMinor half alpha a b c ⟨70+i.val, by omega⟩ 68 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (70+i.val) 0) 564 = 0
  unfold entry
  simp only [show 4*(22+564/3) = 840 from rfl,
    show 1+564%3 = 1 from rfl, show 840+1 = 841 from rfl]
  exact SourceBlockSupport.column147_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 70 144 column147_tail (by decide) i)
#print axioms column147_tail
#print axioms column147_lower

theorem column148_tail : orderedRows.drop 70 = SourceBlockSupport.column148_later := by decide
theorem column148_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 144) :
    orderedMinor half alpha a b c ⟨70+i.val, by omega⟩ 69 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (70+i.val) 0) 565 = 0
  unfold entry
  simp only [show 4*(22+565/3) = 840 from rfl,
    show 1+565%3 = 2 from rfl, show 840+2 = 842 from rfl]
  exact SourceBlockSupport.column148_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 70 144 column148_tail (by decide) i)
#print axioms column148_tail
#print axioms column148_lower

theorem column159_tail : orderedRows.drop 72 = SourceBlockSupport.column159_later := by decide
theorem column159_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 142) :
    orderedMinor half alpha a b c ⟨72+i.val, by omega⟩ 70 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (72+i.val) 0) 617 = 0
  unfold entry
  simp only [show 4*(22+617/3) = 908 from rfl,
    show 1+617%3 = 3 from rfl, show 908+3 = 911 from rfl]
  exact SourceBlockSupport.column159_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 72 142 column159_tail (by decide) i)
#print axioms column159_tail
#print axioms column159_lower

theorem column160_tail : orderedRows.drop 72 = SourceBlockSupport.column160_later := by decide
theorem column160_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 142) :
    orderedMinor half alpha a b c ⟨72+i.val, by omega⟩ 71 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (72+i.val) 0) 618 = 0
  unfold entry
  simp only [show 4*(22+618/3) = 912 from rfl,
    show 1+618%3 = 1 from rfl, show 912+1 = 913 from rfl]
  exact SourceBlockSupport.column160_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 72 142 column160_tail (by decide) i)
#print axioms column160_tail
#print axioms column160_lower

end AspisV8R17.SourceMinor.LowerBlocks
