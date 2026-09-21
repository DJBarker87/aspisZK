import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport11

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column167_tail : orderedRows.drop 90 = SourceBlockSupport.column167_later := by decide
theorem column167_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 124) :
    orderedMinor half alpha a b c ⟨90+i.val, by omega⟩ 88 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (90+i.val) 0) 629 = 0
  unfold entry
  simp only [show 4*(22+629/3) = 924 from rfl,
    show 1+629%3 = 3 from rfl, show 924+3 = 927 from rfl]
  exact SourceBlockSupport.column167_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 90 124 column167_tail (by decide) i)
#print axioms column167_tail
#print axioms column167_lower

theorem column168_tail : orderedRows.drop 90 = SourceBlockSupport.column168_later := by decide
theorem column168_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 124) :
    orderedMinor half alpha a b c ⟨90+i.val, by omega⟩ 89 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (90+i.val) 0) 630 = 0
  unfold entry
  simp only [show 4*(22+630/3) = 928 from rfl,
    show 1+630%3 = 1 from rfl, show 928+1 = 929 from rfl]
  exact SourceBlockSupport.column168_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 90 124 column168_tail (by decide) i)
#print axioms column168_tail
#print axioms column168_lower

theorem column169_tail : orderedRows.drop 92 = SourceBlockSupport.column169_later := by decide
theorem column169_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 122) :
    orderedMinor half alpha a b c ⟨92+i.val, by omega⟩ 90 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (92+i.val) 0) 632 = 0
  unfold entry
  simp only [show 4*(22+632/3) = 928 from rfl,
    show 1+632%3 = 3 from rfl, show 928+3 = 931 from rfl]
  exact SourceBlockSupport.column169_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 92 122 column169_tail (by decide) i)
#print axioms column169_tail
#print axioms column169_lower

theorem column170_tail : orderedRows.drop 92 = SourceBlockSupport.column170_later := by decide
theorem column170_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 122) :
    orderedMinor half alpha a b c ⟨92+i.val, by omega⟩ 91 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (92+i.val) 0) 633 = 0
  unfold entry
  simp only [show 4*(22+633/3) = 932 from rfl,
    show 1+633%3 = 1 from rfl, show 932+1 = 933 from rfl]
  exact SourceBlockSupport.column170_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 92 122 column170_tail (by decide) i)
#print axioms column170_tail
#print axioms column170_lower

theorem column171_tail : orderedRows.drop 94 = SourceBlockSupport.column171_later := by decide
theorem column171_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 120) :
    orderedMinor half alpha a b c ⟨94+i.val, by omega⟩ 92 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (94+i.val) 0) 635 = 0
  unfold entry
  simp only [show 4*(22+635/3) = 932 from rfl,
    show 1+635%3 = 3 from rfl, show 932+3 = 935 from rfl]
  exact SourceBlockSupport.column171_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 94 120 column171_tail (by decide) i)
#print axioms column171_tail
#print axioms column171_lower

theorem column172_tail : orderedRows.drop 94 = SourceBlockSupport.column172_later := by decide
theorem column172_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 120) :
    orderedMinor half alpha a b c ⟨94+i.val, by omega⟩ 93 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (94+i.val) 0) 636 = 0
  unfold entry
  simp only [show 4*(22+636/3) = 936 from rfl,
    show 1+636%3 = 1 from rfl, show 936+1 = 937 from rfl]
  exact SourceBlockSupport.column172_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 94 120 column172_tail (by decide) i)
#print axioms column172_tail
#print axioms column172_lower

theorem column173_tail : orderedRows.drop 96 = SourceBlockSupport.column173_later := by decide
theorem column173_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 118) :
    orderedMinor half alpha a b c ⟨96+i.val, by omega⟩ 94 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (96+i.val) 0) 638 = 0
  unfold entry
  simp only [show 4*(22+638/3) = 936 from rfl,
    show 1+638%3 = 3 from rfl, show 936+3 = 939 from rfl]
  exact SourceBlockSupport.column173_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 96 118 column173_tail (by decide) i)
#print axioms column173_tail
#print axioms column173_lower

theorem column174_tail : orderedRows.drop 96 = SourceBlockSupport.column174_later := by decide
theorem column174_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 118) :
    orderedMinor half alpha a b c ⟨96+i.val, by omega⟩ 95 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (96+i.val) 0) 639 = 0
  unfold entry
  simp only [show 4*(22+639/3) = 940 from rfl,
    show 1+639%3 = 1 from rfl, show 940+1 = 941 from rfl]
  exact SourceBlockSupport.column174_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 96 118 column174_tail (by decide) i)
#print axioms column174_tail
#print axioms column174_lower

end AspisV8R17.SourceMinor.LowerBlocks
