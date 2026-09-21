import AspisV8R17.TailLookup
import AspisV8R17.SourceBlockSupport04

/-! Generated source-matrix lower-block bindings. Inputs:
r17-minor-blocks.jsonl: d3dbd7df5be746dc8d485478be3a733d9cc5cc87b8d150df4e9bf3c6eb1132f8
r17-active-source-rows.json: 2631dc7a00b1577861091cd91be5c8acaa75cbb6828b1dc5eb8ecccb93020bca
r17-active-minor-columns.txt: 3490d677cb0d98f3a0b3f7eef6ad6ad2f6710cb69d205f8a982087aaa2cb6ceb
Uses symbolic tail membership, no repeated full lookup decisions. -/
set_option autoImplicit false
set_option maxRecDepth 2048
namespace AspisV8R17.SourceMinor.LowerBlocks
theorem column112_tail : orderedRows.drop 33 = SourceBlockSupport.column112_later := by decide
theorem column112_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 181) :
    orderedMinor half alpha a b c ⟨33+i.val, by omega⟩ 32 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (33+i.val) 0) 421 = 0
  unfold entry
  simp only [show 4*(22+421/3) = 648 from rfl,
    show 1+421%3 = 2 from rfl, show 648+2 = 650 from rfl]
  exact SourceBlockSupport.column112_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 33 181 column112_tail (by decide) i)
#print axioms column112_tail
#print axioms column112_lower

theorem column110_tail : orderedRows.drop 34 = SourceBlockSupport.column110_later := by decide
theorem column110_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 180) :
    orderedMinor half alpha a b c ⟨34+i.val, by omega⟩ 33 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (34+i.val) 0) 411 = 0
  unfold entry
  simp only [show 4*(22+411/3) = 636 from rfl,
    show 1+411%3 = 1 from rfl, show 636+1 = 637 from rfl]
  exact SourceBlockSupport.column110_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 34 180 column110_tail (by decide) i)
#print axioms column110_tail
#print axioms column110_lower

theorem column114_tail : orderedRows.drop 36 = SourceBlockSupport.column114_later := by decide
theorem column114_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 178) :
    orderedMinor half alpha a b c ⟨36+i.val, by omega⟩ 34 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (36+i.val) 0) 432 = 0
  unfold entry
  simp only [show 4*(22+432/3) = 664 from rfl,
    show 1+432%3 = 1 from rfl, show 664+1 = 665 from rfl]
  exact SourceBlockSupport.column114_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 36 178 column114_tail (by decide) i)
#print axioms column114_tail
#print axioms column114_lower

theorem column115_tail : orderedRows.drop 36 = SourceBlockSupport.column115_later := by decide
theorem column115_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 178) :
    orderedMinor half alpha a b c ⟨36+i.val, by omega⟩ 35 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (36+i.val) 0) 433 = 0
  unfold entry
  simp only [show 4*(22+433/3) = 664 from rfl,
    show 1+433%3 = 2 from rfl, show 664+2 = 666 from rfl]
  exact SourceBlockSupport.column115_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 36 178 column115_tail (by decide) i)
#print axioms column115_tail
#print axioms column115_lower

theorem column113_tail : orderedRows.drop 37 = SourceBlockSupport.column113_later := by decide
theorem column113_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 177) :
    orderedMinor half alpha a b c ⟨37+i.val, by omega⟩ 36 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (37+i.val) 0) 423 = 0
  unfold entry
  simp only [show 4*(22+423/3) = 652 from rfl,
    show 1+423%3 = 1 from rfl, show 652+1 = 653 from rfl]
  exact SourceBlockSupport.column113_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 37 177 column113_tail (by decide) i)
#print axioms column113_tail
#print axioms column113_lower

theorem column117_tail : orderedRows.drop 39 = SourceBlockSupport.column117_later := by decide
theorem column117_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 175) :
    orderedMinor half alpha a b c ⟨39+i.val, by omega⟩ 37 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (39+i.val) 0) 444 = 0
  unfold entry
  simp only [show 4*(22+444/3) = 680 from rfl,
    show 1+444%3 = 1 from rfl, show 680+1 = 681 from rfl]
  exact SourceBlockSupport.column117_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 39 175 column117_tail (by decide) i)
#print axioms column117_tail
#print axioms column117_lower

theorem column118_tail : orderedRows.drop 39 = SourceBlockSupport.column118_later := by decide
theorem column118_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 175) :
    orderedMinor half alpha a b c ⟨39+i.val, by omega⟩ 38 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (39+i.val) 0) 445 = 0
  unfold entry
  simp only [show 4*(22+445/3) = 680 from rfl,
    show 1+445%3 = 2 from rfl, show 680+2 = 682 from rfl]
  exact SourceBlockSupport.column118_zero half (alpha^2) a b c _
    (tail_lookup_mem orderedRows _ 39 175 column118_tail (by decide) i)
#print axioms column118_tail
#print axioms column118_lower

theorem column116_tail : orderedRows.drop 40 = SourceBlockSupport.column116_later := by decide
theorem column116_lower {F : Type*} [CommRing F] (half alpha a b c : F)
    (i : Fin 174) :
    orderedMinor half alpha a b c ⟨40+i.val, by omega⟩ 39 = 0 := by
  rw [orderedMinor_entry]
  change entry half alpha a b c (orderedRows.getD (40+i.val) 0) 435 = 0
  unfold entry
  simp only [show 4*(22+435/3) = 668 from rfl,
    show 1+435%3 = 1 from rfl, show 668+1 = 669 from rfl]
  exact SourceBlockSupport.column116_zero half (alpha^1) a b c _
    (tail_lookup_mem orderedRows _ 40 174 column116_tail (by decide) i)
#print axioms column116_tail
#print axioms column116_lower

end AspisV8R17.SourceMinor.LowerBlocks
