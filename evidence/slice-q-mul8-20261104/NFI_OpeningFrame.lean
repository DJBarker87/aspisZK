import NFC_OpeningFrame
set_option autoImplicit false
namespace AspisR1.NFI_OpeningFrame
open KMX_CopyMeaning

/-- A view is derived from ONE original heap, never passed as an independent
successful opening. The base is the original proof allocation. -/
def opening {α : Type} (heap : Nat → α) (base query : Nat) : Nat → α :=
  fun offset => heap (base+NFC_OpeningFrame.start query+offset)

def view608 {α : Type} (heap : Nat → α) (base query : Nat) : Fin 608 → α :=
  fun byte => opening heap base query byte.val

theorem original_byte {α : Type} (heap : Nat → α) (base query : Nat) (byte : Fin 608) :
    view608 heap base query byte=heap (base+10055+query*832+byte.val) := by
  simp only [view608,opening,NFC_OpeningFrame.start,Nat.add_assoc]

theorem same_heap_frame {α : Type} (before after : Nat → α) (base query : Nat)
    (frame : ∀ offset, offset<832 →
      after (base+NFC_OpeningFrame.start query+offset)=
      before (base+NFC_OpeningFrame.start query+offset)) :
    view608 after base query=view608 before base query := by
  funext byte
  exact frame byte.val (by have h:=byte.isLt; omega)

/-- Arbitrary non-window cells are allowed. The local symbolic-cell check
uses this extensional rule, not an assumption that the other bytes are zero. -/
theorem arbitrary_complement {α : Type} (heap replacement : Nat → α) (base query : Nat)
    (same : ∀ byte : Fin 608,
      replacement (base+NFC_OpeningFrame.start query+byte.val)=
      heap (base+NFC_OpeningFrame.start query+byte.val)) :
    view608 replacement base query=view608 heap base query := by
  funext byte; exact same byte

/-- Real receiver/output writes may be composed only after native disjointness
has been established for those same allocations. -/
theorem receiver_and_return_frame {α : Type} (a b c result heap : Nat → α)
    (base query receiver size output outputSize : Nat)
    (receiverDisjoint : base+NFC_OpeningFrame.start query+832≤receiver ∨
      receiver+size≤base+NFC_OpeningFrame.start query)
    (outputDisjoint : base+NFC_OpeningFrame.start query+832≤output ∨
      output+outputSize≤base+NFC_OpeningFrame.start query) :
    view608 (loop result (NFC_KmxFrames.three a b c heap receiver size) output outputSize)
      base query=view608 heap base query := by
  funext byte
  exact NFC_KmxFrames.output_frame a b c result heap receiver size output outputSize
    (base+NFC_OpeningFrame.start query) 832 receiverDisjoint outputDisjoint byte.val
    (by have h:=byte.isLt; omega)

#print axioms original_byte
#print axioms same_heap_frame
#print axioms arbitrary_complement
#print axioms receiver_and_return_frame
end AspisR1.NFI_OpeningFrame
