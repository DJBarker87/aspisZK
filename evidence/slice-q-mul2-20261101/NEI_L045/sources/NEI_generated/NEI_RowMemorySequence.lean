import NEI_RowMemoryWindows
set_option autoImplicit false
namespace NEI_RowMemorySequence
/-- Compose actual indexed-write value relations in their native order. No
assumption is made about the values produced inside the selected row. -/
def writes {α : Type} : List (Nat × α) → (Nat → α) → Nat → α
 | [], mem => mem
 | (address,value)::tail, mem => writes tail (KMX_CopyMeaning.write mem address value)

theorem outside {α : Type} (updates : List (Nat × α)) (mem : Nat → α) (at : Nat)
 (different : ∀ update ∈ updates, at ≠ update.1) : writes updates mem at=mem at := by
 induction updates generalizing mem with
 | nil => rfl
 | cons head tail ih =>
  rw [writes,ih]
  · exact if_neg (different head (by simp))
  · intro update member
    exact different update (by simp [member])

theorem within_word (row lane byte : Nat) (hl : lane<4) (hb : byte<8) :
 row*32 ≤ row*32+lane*8+byte ∧ row*32+lane*8+byte<row*32+32 := by omega

theorem row_frame {α : Type} (updates : List (Nat × α)) (mem : Nat → α)
 (selected observed byte : Nat) (different : observed ≠ selected) (hb : byte<32)
 (inside : ∀ update ∈ updates, selected*32 ≤ update.1 ∧ update.1<selected*32+32) :
 writes updates mem (observed*32+byte)=mem (observed*32+byte) := by
 apply outside
 intro update member
 have h := inside update member
 have d := NEI_RowMemoryWindows.disjoint selected observed byte different hb
 omega
#print axioms outside
#print axioms within_word
#print axioms row_frame
end NEI_RowMemorySequence
