import KMX_CopyMeaning
set_option autoImplicit false
namespace NFC_KmxFrames
open KMX_CopyMeaning
/-- Three source-ordered copies into the SAME receiver region. This value
law retains pointer validity, ownership and physical disjointness as admissions. -/
def three {α : Type} (a b c heap : Nat → α) (start count : Nat) : Nat → α :=
  loop c (loop b (loop a heap start count) start count) start count

theorem final_region {α : Type} (a b c heap : Nat → α) (start count k : Nat)
    (inside : start≤k ∧ k<start+count) : three a b c heap start count k=c k := by
  unfold three
  rw [loop_spec,if_pos inside]

theorem frame {α : Type} (a b c heap : Nat → α) (start count k : Nat)
    (outside : k<start ∨ start+count≤k) : three a b c heap start count k=heap k := by
  unfold three
  rw [copy_frame _ _ start count k outside,copy_frame _ _ start count k outside,
    copy_frame _ _ start count k outside]

/-- Any source window disjoint from the receiver survives all three calls. -/
theorem source_window {α : Type} (a b c heap : Nat → α)
    (receiver size source width : Nat)
    (disjoint : source+width≤receiver ∨ receiver+size≤source) :
    ∀ offset,width>offset →
      three a b c heap receiver size (source+offset)=heap (source+offset) := by
  intro offset bounded
  apply frame
  omega

/-- A fourth output copy also frames the original source window. -/
theorem output_frame {α : Type} (a b c result heap : Nat → α)
    (receiver size output outputSize source width : Nat)
    (receiverDisjoint : source+width≤receiver ∨ receiver+size≤source)
    (outputDisjoint : source+width≤output ∨ output+outputSize≤source)
    (offset : Nat) (bounded : offset<width) :
    loop result (three a b c heap receiver size) output outputSize (source+offset)=heap (source+offset) := by
  rw [copy_frame _ _ output outputSize (source+offset) (by omega)]
  exact source_window a b c heap receiver size source width receiverDisjoint offset bounded
#print axioms final_region
#print axioms frame
#print axioms source_window
#print axioms output_frame
end NFC_KmxFrames
