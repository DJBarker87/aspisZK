import NBJ_Audit
import Std

set_option autoImplicit false
namespace AspisR1.NBV_WindowFrame

/-- Replacing one window leaves every disjoint opening unchanged, even when
all surrounding bytes are arbitrary. This is a value/frame fact only. -/
def install {α : Type} (memory window : Nat → α) (base width : Nat) : Nat → α :=
  fun k => if base ≤ k ∧ k < base+width then window (k-base) else memory k

theorem opening_disjoint (i j c : Nat) (different : i ≠ j)
    (byte : c < 832) :
    ¬ (10055+832*j ≤ 10055+832*i+c ∧
       10055+832*i+c < 10055+832*j+832) := by omega

theorem opening_frame {α : Type} (memory window : Nat → α)
    (i j c : Nat) (different : i ≠ j) (byte : c < 832) :
    install memory window (10055+832*j) 832 (10055+832*i+c) =
      memory (10055+832*i+c) := by
  exact if_neg (opening_disjoint i j c different byte)

/-- A selected window from the SAME memory needs no zero-surroundings premise. -/
theorem selected_window {α : Type} (memory : Nat → α)
    (base width c : Nat) (byte : c < width) :
    install memory (fun k => memory (base+k)) base width (base+c) = memory (base+c) := by
  have range : base ≤ base+c ∧ base+c < base+width := by omega
  simp only [install,if_pos range,Nat.add_sub_cancel_left]

/-- Store disjointness is independent of the values of every unread row. -/
theorem row_frame {α : Type} (memory : Nat → α) (value : α)
    (write read : Nat) (disjoint : write ≠ read) :
    (fun k => if k = write then value else memory k) read = memory read := by
  exact if_neg (Ne.symm disjoint)

#print axioms opening_disjoint
#print axioms opening_frame
#print axioms selected_window
#print axioms row_frame
end AspisR1.NBV_WindowFrame
