import LPr_SelectedBytes
set_option autoImplicit false
namespace AspisR1.LPr_SelectedWords
open Aeneas Aeneas.Std Result

def byte (bs : List U8) (i : Nat) : U8 := bs[i]?.getD 0#u8

def naturalWord (bs : List U8) (i : Nat) : Nat :=
  (byte bs i).val + 256*(byte bs (i+1)).val +
    65536*(byte bs (i+2)).val + 16777216*(byte bs (i+3)).val

def nativeWord (b : Slice U8) (j : Nat) : U32 := core.num.U32.from_le_bytes
  (Array.make 4#usize [byte b.val (4*j),byte b.val (4*j+1),
    byte b.val (4*j+2),byte b.val (4*j+3)])

theorem window_byte (bs : List U8) (offset lane : Nat) (h : lane<32) :
    byte ((bs.drop offset).take 32) lane = byte bs (offset+lane) := by
  simp only [byte,List.getElem?_take,h,↓reduceIte,List.getElem?_drop]

theorem window_word (bs : List U8) (b : Slice U8) (offset j : Nat)
    (same : b.val=(bs.drop offset).take 32) (hj : j<8) :
    (nativeWord b j).val=naturalWord bs (offset+4*j) := by
  unfold nativeWord
  rw [LPr_WordNat.value]
  simp only [same,window_byte bs offset (4*j) (by omega),
    window_byte bs offset (4*j+1) (by omega),
    window_byte bs offset (4*j+2) (by omega),
    window_byte bs offset (4*j+3) (by omega),naturalWord,Nat.add_assoc]

/-- Converts global natural LE word bounds into the exact native selected-byte
    domain. It does not claim the still-uninstalled check/expand caller join. -/
theorem selected_words (y1 : Slice U8) (len : y1.val.length=928)
    (canonical : ∀ row j : Nat, row<29 → j<8 →
      naturalWord y1.val (32*row+4*j)<2147483647) :
    ∀ l : Usize, l.val<29 → ∃ b : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) y1
        {start:=Usize.wrapping_mul l 32#usize,
         «end»:=Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize}=ok b ∧
      b.val.length=32 ∧ (∀ j, j<8 → (nativeWord b j).val<2147483647) := by
  intro l hl
  obtain ⟨b,run,size,same⟩ := LPr_SelectedBytes.selected y1 len l hl
  refine ⟨b,run,size,?_⟩
  intro j hj
  rw [window_word y1.val b (32*l.val) j same hj]
  exact canonical l.val j hl hj

#print axioms window_byte
#print axioms window_word
#print axioms selected_words
end AspisR1.LPr_SelectedWords
