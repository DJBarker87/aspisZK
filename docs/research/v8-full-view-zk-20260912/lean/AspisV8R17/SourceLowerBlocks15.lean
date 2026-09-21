import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport15

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column199_tail : orderedRows.drop 122 = SourceBlockSupport.column199_later := by decide
theorem column199_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 92) :
    orderedMinor half alpha a b c ⟨122+i.val, by omega⟩ 120 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (122+i.val) 0) 677 = 0
  unfold entry
  simp only [show 4*(22+677/3) = 988 from rfl,
    show 1+677%3 = 3 from rfl, show 988+3 = 991 from rfl]
  exact SourceBlockSupport.column199_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 122 92 column199_tail (by decide) i)
#print axioms column199_tail
#print axioms column199_lower

theorem column200_tail : orderedRows.drop 122 = SourceBlockSupport.column200_later := by decide
theorem column200_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 92) :
    orderedMinor half alpha a b c ⟨122+i.val, by omega⟩ 121 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (122+i.val) 0) 678 = 0
  unfold entry
  simp only [show 4*(22+678/3) = 992 from rfl,
    show 1+678%3 = 1 from rfl, show 992+1 = 993 from rfl]
  exact SourceBlockSupport.column200_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 122 92 column200_tail (by decide) i)
#print axioms column200_tail
#print axioms column200_lower

theorem column17_tail : orderedRows.drop 123 = SourceBlockSupport.column17_later := by decide
theorem column17_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 91) :
    orderedMinor half alpha a b c ⟨123+i.val, by omega⟩ 122 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (123+i.val) 0) 65 = 0
  unfold entry
  simp only [show 4*(22+65/3) = 172 from rfl,
    show 1+65%3 = 3 from rfl, show 172+3 = 175 from rfl]
  exact SourceBlockSupport.column17_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 123 91 column17_tail (by decide) i)
#print axioms column17_tail
#print axioms column17_lower

theorem column201_tail : orderedRows.drop 125 = SourceBlockSupport.column201_later := by decide
theorem column201_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 89) :
    orderedMinor half alpha a b c ⟨125+i.val, by omega⟩ 123 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (125+i.val) 0) 680 = 0
  unfold entry
  simp only [show 4*(22+680/3) = 992 from rfl,
    show 1+680%3 = 3 from rfl, show 992+3 = 995 from rfl]
  exact SourceBlockSupport.column201_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 125 89 column201_tail (by decide) i)
#print axioms column201_tail
#print axioms column201_lower

theorem column202_tail : orderedRows.drop 125 = SourceBlockSupport.column202_later := by decide
theorem column202_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 89) :
    orderedMinor half alpha a b c ⟨125+i.val, by omega⟩ 124 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (125+i.val) 0) 681 = 0
  unfold entry
  simp only [show 4*(22+681/3) = 996 from rfl,
    show 1+681%3 = 1 from rfl, show 996+1 = 997 from rfl]
  exact SourceBlockSupport.column202_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 125 89 column202_tail (by decide) i)
#print axioms column202_tail
#print axioms column202_lower

theorem column203_tail : orderedRows.drop 127 = SourceBlockSupport.column203_later := by decide
theorem column203_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 87) :
    orderedMinor half alpha a b c ⟨127+i.val, by omega⟩ 125 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (127+i.val) 0) 683 = 0
  unfold entry
  simp only [show 4*(22+683/3) = 996 from rfl,
    show 1+683%3 = 3 from rfl, show 996+3 = 999 from rfl]
  exact SourceBlockSupport.column203_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 127 87 column203_tail (by decide) i)
#print axioms column203_tail
#print axioms column203_lower

theorem column204_tail : orderedRows.drop 127 = SourceBlockSupport.column204_later := by decide
theorem column204_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 87) :
    orderedMinor half alpha a b c ⟨127+i.val, by omega⟩ 126 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (127+i.val) 0) 684 = 0
  unfold entry
  simp only [show 4*(22+684/3) = 1000 from rfl,
    show 1+684%3 = 1 from rfl, show 1000+1 = 1001 from rfl]
  exact SourceBlockSupport.column204_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 127 87 column204_tail (by decide) i)
#print axioms column204_tail
#print axioms column204_lower

theorem column22_tail : orderedRows.drop 128 = SourceBlockSupport.column22_later := by decide
theorem column22_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 86) :
    orderedMinor half alpha a b c ⟨128+i.val, by omega⟩ 127 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (128+i.val) 0) 77 = 0
  unfold entry
  simp only [show 4*(22+77/3) = 188 from rfl,
    show 1+77%3 = 3 from rfl, show 188+3 = 191 from rfl]
  exact SourceBlockSupport.column22_zero half (alpha^3) a b c _
    (tail_lookup_mem orderedRows _ 128 86 column22_tail (by decide) i)
#print axioms column22_tail
#print axioms column22_lower

end AspisV8R17.SourceMinor.LowerBlocks
