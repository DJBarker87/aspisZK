import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport14

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column191_tail : orderedRows.drop 114 = SourceBlockSupport.column191_later := by decide
theorem column191_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 100) :
    orderedMinor half alpha a b c ⟨114+i.val, by omega⟩ 112 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (114+i.val) 0) 665 = 0
  unfold entry
  simp only [show 4*(22+665/3) = 972 from rfl,
    show 1+665%3 = 3 from rfl, show 972+3 = 975 from rfl]
  exact SourceBlockSupport.column191_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 114 100 column191_tail (by decide) i)
#print axioms column191_tail
#print axioms column191_lower

theorem column192_tail : orderedRows.drop 114 = SourceBlockSupport.column192_later := by decide
theorem column192_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 100) :
    orderedMinor half alpha a b c ⟨114+i.val, by omega⟩ 113 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (114+i.val) 0) 666 = 0
  unfold entry
  simp only [show 4*(22+666/3) = 976 from rfl,
    show 1+666%3 = 1 from rfl, show 976+1 = 977 from rfl]
  exact SourceBlockSupport.column192_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 114 100 column192_tail (by decide) i)
#print axioms column192_tail
#print axioms column192_lower

theorem column193_tail : orderedRows.drop 116 = SourceBlockSupport.column193_later := by decide
theorem column193_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 98) :
    orderedMinor half alpha a b c ⟨116+i.val, by omega⟩ 114 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (116+i.val) 0) 668 = 0
  unfold entry
  simp only [show 4*(22+668/3) = 976 from rfl,
    show 1+668%3 = 3 from rfl, show 976+3 = 979 from rfl]
  exact SourceBlockSupport.column193_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 116 98 column193_tail (by decide) i)
#print axioms column193_tail
#print axioms column193_lower

theorem column194_tail : orderedRows.drop 116 = SourceBlockSupport.column194_later := by decide
theorem column194_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 98) :
    orderedMinor half alpha a b c ⟨116+i.val, by omega⟩ 115 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (116+i.val) 0) 669 = 0
  unfold entry
  simp only [show 4*(22+669/3) = 980 from rfl,
    show 1+669%3 = 1 from rfl, show 980+1 = 981 from rfl]
  exact SourceBlockSupport.column194_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 116 98 column194_tail (by decide) i)
#print axioms column194_tail
#print axioms column194_lower

theorem column195_tail : orderedRows.drop 118 = SourceBlockSupport.column195_later := by decide
theorem column195_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 96) :
    orderedMinor half alpha a b c ⟨118+i.val, by omega⟩ 116 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (118+i.val) 0) 671 = 0
  unfold entry
  simp only [show 4*(22+671/3) = 980 from rfl,
    show 1+671%3 = 3 from rfl, show 980+3 = 983 from rfl]
  exact SourceBlockSupport.column195_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 118 96 column195_tail (by decide) i)
#print axioms column195_tail
#print axioms column195_lower

theorem column196_tail : orderedRows.drop 118 = SourceBlockSupport.column196_later := by decide
theorem column196_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 96) :
    orderedMinor half alpha a b c ⟨118+i.val, by omega⟩ 117 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (118+i.val) 0) 672 = 0
  unfold entry
  simp only [show 4*(22+672/3) = 984 from rfl,
    show 1+672%3 = 1 from rfl, show 984+1 = 985 from rfl]
  exact SourceBlockSupport.column196_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 118 96 column196_tail (by decide) i)
#print axioms column196_tail
#print axioms column196_lower

theorem column197_tail : orderedRows.drop 120 = SourceBlockSupport.column197_later := by decide
theorem column197_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 94) :
    orderedMinor half alpha a b c ⟨120+i.val, by omega⟩ 118 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (120+i.val) 0) 674 = 0
  unfold entry
  simp only [show 4*(22+674/3) = 984 from rfl,
    show 1+674%3 = 3 from rfl, show 984+3 = 987 from rfl]
  exact SourceBlockSupport.column197_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 120 94 column197_tail (by decide) i)
#print axioms column197_tail
#print axioms column197_lower

theorem column198_tail : orderedRows.drop 120 = SourceBlockSupport.column198_later := by decide
theorem column198_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 94) :
    orderedMinor half alpha a b c ⟨120+i.val, by omega⟩ 119 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (120+i.val) 0) 675 = 0
  unfold entry
  simp only [show 4*(22+675/3) = 988 from rfl,
    show 1+675%3 = 1 from rfl, show 988+1 = 989 from rfl]
  exact SourceBlockSupport.column198_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 120 94 column198_tail (by decide) i)
#print axioms column198_tail
#print axioms column198_lower

end AspisV8R17.SourceMinor.LowerBlocks
