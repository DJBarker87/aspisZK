import NIO_Nested
set_option autoImplicit false
namespace NIO_AbortScopes
open NIO_Nested

/-- Extra child errors can end a scoped prefix; the child counter frame is
represented here by leaving counters unchanged before the chosen abort. -/
def run (s : Nat → Int) (abort : Nat → Bool) (stage : Nat) :
    List Nat → Bool × (Nat → Int)
  | [] => (!abort stage,s)
  | c :: tail =>
    if s c = 0 then
      if abort stage then (false,put (put s c (-1)) c 0)
      else
        let result := run (put s c (-1)) abort (stage+1) tail
        (result.1,put result.2 c 0)
    else (false,s)

theorem cleanup_all_abort_prefixes (s : Nat → Int) (abort : Nat → Bool)
    (stage : Nat) (cells : List Nat) : (run s abort stage cells).2 = s := by
  induction cells generalizing s stage with
  | nil => rfl
  | cons c tail ih =>
    by_cases free : s c = 0
    · simp only [run,if_pos free]
      split
      · exact put_restore s c free
      · rw [ih]
        exact put_restore s c free
    · simp only [run,if_neg free]
#print axioms cleanup_all_abort_prefixes

theorem shared_room_after_abort (s : Nat → Int) (abort : Nat → Bool)
    (stage : Nat) (cells : List Nat) (a : Nat) (cap : Int)
    (room : 0 ≤ s a ∧ s a < cap) :
    0 ≤ (run s abort stage cells).2 a ∧ (run s abort stage cells).2 a < cap := by
  rw [cleanup_all_abort_prefixes]
  exact room
#print axioms shared_room_after_abort
end NIO_AbortScopes
