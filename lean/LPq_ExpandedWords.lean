import LPq_ReadPorts
set_option autoImplicit false
namespace AspisR1.LPq_ExpandedWords
open Aeneas Aeneas.Std Result

def byte (bs : List U8) (i : Nat) : Nat := (bs[i]?.getD 0#u8).val
def word (bs : List U8) (i : Nat) : Nat :=
  byte bs i + 256*byte bs (i+1) + 65536*byte bs (i+2) + 16777216*byte bs (i+3)

/-- Exactly the low16-copy/high16-zero postcondition of the CLOSED LPn
expand_values leaf on the same compact and expanded carriers. -/
def Expanded (compact y1 : List U8) : Prop := ∀ row, row<29 → ∀ lane, lane<32 →
  byte y1 (32*row+lane)=if lane<16 then byte compact (16*row+lane) else 0

def CompactCanonical (compact : List U8) : Prop := ∀ row, row<29 → ∀ limb,
  limb<4 → word compact (16*row+4*limb)<2147483647

theorem low (compact y1 : List U8) (h : Expanded compact y1) (row limb : Nat)
    (hr : row<29) (hl : limb<4) :
    word y1 (32*row+4*limb)=word compact (16*row+4*limb) := by
  have b0 := h row hr (4*limb) (by omega)
  have b1 := h row hr (4*limb+1) (by omega)
  have b2 := h row hr (4*limb+2) (by omega)
  have b3 := h row hr (4*limb+3) (by omega)
  simp only [if_pos (show 4*limb<16 by omega)] at b0
  simp only [if_pos (show 4*limb+1<16 by omega)] at b1
  simp only [if_pos (show 4*limb+2<16 by omega)] at b2
  simp only [if_pos (show 4*limb+3<16 by omega)] at b3
  simp only [word,Nat.add_assoc,b0,b1,b2,b3]

theorem high (compact y1 : List U8) (h : Expanded compact y1) (row limb : Nat)
    (hr : row<29) (hl : 4≤limb) (hu : limb<8) : word y1 (32*row+4*limb)=0 := by
  have b0 := h row hr (4*limb) (by omega)
  have b1 := h row hr (4*limb+1) (by omega)
  have b2 := h row hr (4*limb+2) (by omega)
  have b3 := h row hr (4*limb+3) (by omega)
  simp only [if_neg (show ¬ (4*limb<16) by omega)] at b0
  simp only [if_neg (show ¬ (4*limb+1<16) by omega)] at b1
  simp only [if_neg (show ¬ (4*limb+2<16) by omega)] at b2
  simp only [if_neg (show ¬ (4*limb+3<16) by omega)] at b3
  simp only [word,Nat.add_assoc,b0,b1,b2,b3,Nat.mul_zero,Nat.add_zero]

theorem canonical (compact y1 : List U8) (h : Expanded compact y1)
    (hc : CompactCanonical compact) (row limb : Nat) (hr : row<29) (hl : limb<8) :
    word y1 (32*row+4*limb)<2147483647 := by
  by_cases small : limb<4
  · rw [low compact y1 h row limb hr small];exact hc row hr limb small
  · rw [high compact y1 h row limb hr (by omega) hl];decide

#print axioms low
#print axioms high
#print axioms canonical
end AspisR1.LPq_ExpandedWords
