import NFQ_ZeroStep
import NFQ_ZeroSource
set_option autoImplicit false
namespace NFT_ZeroPhysical
open Aeneas Aeneas.Std Result

def pad (bytes : List U8) : List U8 := bytes ++ List.replicate (4096-bytes.length) 0#u8

theorem pad_length (bytes : List U8) (bound : bytes.length≤4096) : (pad bytes).length=4096 := by
  simp only [pad,List.length_append,List.length_replicate]
  omega

theorem take_append_bounded {α : Type} (xs ys : List α) (n : Nat) (bound : n≤xs.length) :
    (xs++ys).take n=xs.take n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => simp at bound
    | cons x xs =>
      simp only [List.cons_append,List.take_succ_cons]
      exact congrArg (List.cons x) (ih xs (by simpa using bound))

theorem window_pad (bytes : List U8) (start count : Nat) (inside : start+count≤bytes.length) :
    ((pad bytes).drop start).take count=(bytes.drop start).take count := by
  simp only [List.take_drop,pad]
  exact congrArg (List.drop start) (take_append_bounded bytes _ (start+count) inside)

theorem suffix_pad (bytes : List U8) (start : Nat) (inside : start≤bytes.length) :
    ((pad bytes).drop start).take (bytes.length-start)=bytes.drop start := by
  rw [window_pad bytes start (bytes.length-start) (by omega)]
  exact List.take_of_length_le (by simp only [List.length_drop];omega)

structure Surface (Allocation : Type) where
  allocation : Allocation
  bytes : List U8
  offset : Nat

def advance {A : Type} (s : Surface A) : Surface A := {s with offset:=s.offset+1}
def view {A : Type} (s : Surface A) : List U8 := s.bytes.drop s.offset
def pointer {A : Type} (s : Surface A) : A × Nat := (s.allocation,s.offset)

theorem pointer_step {A : Type} (s : Surface A) : pointer (advance s)=(s.allocation,s.offset+1) := rfl

theorem slice_step {A : Type} (s : Surface A) : view (advance s)=(view s).drop 1 := by
  simp only [view,advance,List.drop_drop]

theorem length_step {A : Type} (s : Surface A) (inside : s.offset<s.bytes.length) :
    (view (advance s)).length=(view s).length-1 := by
  simp only [view,advance,List.length_drop]
  omega

theorem frame {A : Type} (s : Surface A) :
    (advance s).allocation=s.allocation ∧ (advance s).bytes=s.bytes := ⟨rfl,rfl⟩

/-- Every reached suffix has exactly its original bytes in the 4096-byte
bounded native representation; ghost padding is never in the visible view. -/
theorem physical_view {A : Type} (s : Surface A) (bound : s.bytes.length≤4096)
    (inside : s.offset≤s.bytes.length) :
    (pad s.bytes).length=4096 ∧
      ((pad s.bytes).drop s.offset).take (s.bytes.length-s.offset)=view s ∧
      pointer s=(s.allocation,s.offset) :=
  ⟨pad_length _ bound,suffix_pad _ _ inside,rfl⟩

#print axioms pad_length
#print axioms take_append_bounded
#print axioms window_pad
#print axioms suffix_pad
#print axioms pointer_step
#print axioms slice_step
#print axioms length_step
#print axioms frame
#print axioms physical_view
end NFT_ZeroPhysical
