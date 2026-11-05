import NIO_Infos
set_option autoImplicit false
namespace NIO_Nested

def put (s : Nat → Int) (c : Nat) (v : Int) : Nat → Int :=
  fun d => if d = c then v else s d

/-- Reference control for fallible exclusive acquisition and ordinary scoped cleanup.
No account accessor or child footprint is licensed by this definition. -/
def run (s : Nat → Int) : List Nat → Bool × (Nat → Int)
  | [] => (true,s)
  | c :: tail =>
    if s c = 0 then
      let result := run (put s c (-1)) tail
      (result.1,put result.2 c 0)
    else (false,s)

theorem put_restore (s : Nat → Int) (c : Nat) (free : s c = 0) :
    put (put s c (-1)) c 0 = s := by
  funext d
  by_cases h : d = c
  · subst d
    simp [put,free]
  · simp [put,h]
#print axioms put_restore

/-- Includes failed acquisitions and aliased requested cells, on every counter state. -/
theorem cleanup_all_counters (s : Nat → Int) (cells : List Nat) :
    (run s cells).2 = s := by
  induction cells generalizing s with
  | nil => rfl
  | cons c tail ih =>
    by_cases free : s c = 0
    · simp only [run,if_pos free]
      rw [ih]
      exact put_restore s c free
    · simp only [run,if_neg free]
#print axioms cleanup_all_counters

/-- A repeated physical cell is rejected; it need not be assumed distinct to
prove cleanup. This does not certify any infallible accessor between acquisitions. -/
theorem repeated_head_rejects (s : Nat → Int) (c : Nat) (tail : List Nat) :
    (run s (c :: c :: tail)).1 = false := by
  by_cases free : s c = 0
  · simp [run,free,put]
  · simp [run,free]
#print axioms repeated_head_rejects

/-- One retained-Vec acquisition preserves all already-held counters. -/
theorem retained_step (s : Nat → Int) (held : List Nat) (c : Nat)
    (prior : ∀ d ∈ held, s d = -1) (free : s c = 0) :
    c ∉ held ∧ ∀ d ∈ held, put s c (-1) d = -1 := by
  have fresh : c ∉ held := by
    intro member
    have h := prior c member
    omega
  refine ⟨fresh,?_⟩
  intro d member
  have ne : d ≠ c := by
    intro same
    subst d
    exact fresh member
  simp only [put,if_neg ne]
  exact prior d member
#print axioms retained_step

/-- Counter cleanup commutes, including the forward order used by retained carriers. -/
theorem cleanup_commutes (s : Nat → Int) (a b : Nat) :
    put (put s a 0) b 0 = put (put s b 0) a 0 := by
  funext d
  by_cases ha : d = a <;> by_cases hb : d = b <;> simp [put,ha,hb]
#print axioms cleanup_commutes
end NIO_Nested
