import PV_EVH_StackEntropyCoherence
set_option autoImplicit false
namespace PV_EVH_EntropySourceSlot
open PV_EVH_StackZero (Slot State)

/-- A ghost lifetime identity, independent of the source array's contents and
physical address. Retired entries are included so repeated loop iterations do
not reuse an identity, even when the machine reuses the same stack address. -/
def frontier : List Slot → Nat
  | [] => 0
  | s :: rest => max (s.key.identity+1) (frontier rest)

theorem identity_lt (slots : List Slot) (s : Slot) (hs : s ∈ slots) :
    s.key.identity < frontier slots := by
  induction slots with
  | nil => cases hs
  | cons old rest ih =>
    rcases List.mem_cons.mp hs with h | h
    · subst s
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right _ _)

/-- The frozen source creates a fresh zero-initialized [u8;64] lifetime here.
Address is supplied by source-frame provenance, never synthesized from bytes
or from a convenient unoccupied numeric address. Owner is the enclosing frame. -/
def original (owner address : Nat) (w : State) : Slot :=
  ⟨⟨frontier (w.frame.live ++ w.frame.retired),owner⟩,address,64⟩

theorem fresh (owner address : Nat) (w : State) :
    PV_EVH_StackEntropyCoherence.Fresh (original owner address w) w := by
  intro old ho heq
  have hi := identity_lt (w.frame.live ++ w.frame.retired) old (List.mem_append_left _ ho)
  have hk := congrArg PV_EVH_HeapOwnership.Key.identity heq
  change old.key.identity = frontier (w.frame.live ++ w.frame.retired) at hk
  omega

theorem admission (owner address : Nat) (w : State)
    (heap : PV_EVH_StackAdmission.HeapSeparate (original owner address w) w)
    (live : PV_EVH_StackAdmission.LiveSeparate (original owner address w) w) :
    PV_EVH_StackEntropyCoherence.Admission (original owner address w) w :=
  ⟨rfl,fresh owner address w,heap,live⟩

#print axioms identity_lt
#print axioms fresh
#print axioms admission
end PV_EVH_EntropySourceSlot
