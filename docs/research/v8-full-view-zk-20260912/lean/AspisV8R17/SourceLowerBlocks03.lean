import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport03

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column101_tail : orderedRows.drop 25 = SourceBlockSupport.column101_later := by decide
theorem column101_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 189) :
    orderedMinor half alpha a b c ⟨25+i.val, by omega⟩ 24 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (25+i.val) 0) 375 = 0
  unfold entry
  simp only [show 4*(22+375/3) = 588 from rfl,
    show 1+375%3 = 1 from rfl, show 588+1 = 589 from rfl]
  exact SourceBlockSupport.column101_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 25 189 column101_tail (by decide) i)
#print axioms column101_tail
#print axioms column101_lower

theorem column105_tail : orderedRows.drop 27 = SourceBlockSupport.column105_later := by decide
theorem column105_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 187) :
    orderedMinor half alpha a b c ⟨27+i.val, by omega⟩ 25 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (27+i.val) 0) 396 = 0
  unfold entry
  simp only [show 4*(22+396/3) = 616 from rfl,
    show 1+396%3 = 1 from rfl, show 616+1 = 617 from rfl]
  exact SourceBlockSupport.column105_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 27 187 column105_tail (by decide) i)
#print axioms column105_tail
#print axioms column105_lower

theorem column106_tail : orderedRows.drop 27 = SourceBlockSupport.column106_later := by decide
theorem column106_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 187) :
    orderedMinor half alpha a b c ⟨27+i.val, by omega⟩ 26 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (27+i.val) 0) 397 = 0
  unfold entry
  simp only [show 4*(22+397/3) = 616 from rfl,
    show 1+397%3 = 2 from rfl, show 616+2 = 618 from rfl]
  exact SourceBlockSupport.column106_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 27 187 column106_tail (by decide) i)
#print axioms column106_tail
#print axioms column106_lower

theorem column104_tail : orderedRows.drop 28 = SourceBlockSupport.column104_later := by decide
theorem column104_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 186) :
    orderedMinor half alpha a b c ⟨28+i.val, by omega⟩ 27 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (28+i.val) 0) 387 = 0
  unfold entry
  simp only [show 4*(22+387/3) = 604 from rfl,
    show 1+387%3 = 1 from rfl, show 604+1 = 605 from rfl]
  exact SourceBlockSupport.column104_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 28 186 column104_tail (by decide) i)
#print axioms column104_tail
#print axioms column104_lower

theorem column108_tail : orderedRows.drop 30 = SourceBlockSupport.column108_later := by decide
theorem column108_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 184) :
    orderedMinor half alpha a b c ⟨30+i.val, by omega⟩ 28 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (30+i.val) 0) 408 = 0
  unfold entry
  simp only [show 4*(22+408/3) = 632 from rfl,
    show 1+408%3 = 1 from rfl, show 632+1 = 633 from rfl]
  exact SourceBlockSupport.column108_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 30 184 column108_tail (by decide) i)
#print axioms column108_tail
#print axioms column108_lower

theorem column109_tail : orderedRows.drop 30 = SourceBlockSupport.column109_later := by decide
theorem column109_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 184) :
    orderedMinor half alpha a b c ⟨30+i.val, by omega⟩ 29 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (30+i.val) 0) 409 = 0
  unfold entry
  simp only [show 4*(22+409/3) = 632 from rfl,
    show 1+409%3 = 2 from rfl, show 632+2 = 634 from rfl]
  exact SourceBlockSupport.column109_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 30 184 column109_tail (by decide) i)
#print axioms column109_tail
#print axioms column109_lower

theorem column107_tail : orderedRows.drop 31 = SourceBlockSupport.column107_later := by decide
theorem column107_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 183) :
    orderedMinor half alpha a b c ⟨31+i.val, by omega⟩ 30 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (31+i.val) 0) 399 = 0
  unfold entry
  simp only [show 4*(22+399/3) = 620 from rfl,
    show 1+399%3 = 1 from rfl, show 620+1 = 621 from rfl]
  exact SourceBlockSupport.column107_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 31 183 column107_tail (by decide) i)
#print axioms column107_tail
#print axioms column107_lower

theorem column111_tail : orderedRows.drop 33 = SourceBlockSupport.column111_later := by decide
theorem column111_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 181) :
    orderedMinor half alpha a b c ⟨33+i.val, by omega⟩ 31 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (33+i.val) 0) 420 = 0
  unfold entry
  simp only [show 4*(22+420/3) = 648 from rfl,
    show 1+420%3 = 1 from rfl, show 648+1 = 649 from rfl]
  exact SourceBlockSupport.column111_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 33 181 column111_tail (by decide) i)
#print axioms column111_tail
#print axioms column111_lower

end AspisV8R17.SourceMinor.LowerBlocks
