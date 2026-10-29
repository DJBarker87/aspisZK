import PV_L2E_DivisionTrace
set_option autoImplicit false
namespace PV_L2E_DigitsTrace
open PV_L2D_DivisionBounds

structure Output where
  quotient : List Nat
  digits : List Nat
  events : List PV_L2E_DivisionTrace.Event

/-- `count` is 4 for qm31 and 8 for ordinary/gamma. A quotient pass always
starts at remainder zero and traverses all eight words. -/
def run : Nat → List Nat → Output
  | 0,xs => ⟨xs,[],[]⟩
  | n+1,xs =>
    let p := PV_L2E_DivisionTrace.run xs.length 0 xs
    let rest := run n p.1.1
    ⟨rest.quotient,p.1.2::rest.digits,p.2 ++ rest.events⟩

def plan : Nat → Nat → List PV_L2E_DivisionTrace.Event
  | 0,_ => []
  | n+1,width => PV_L2E_DivisionTrace.plan width ++ plan n width

theorem quotient_length (n : Nat) (xs : List Nat) :
    (run n xs).quotient.length=xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    simp only [run,ih,PV_L2E_DivisionTrace.complete_value,pass_length]

theorem digit_count (n : Nat) (xs : List Nat) : (run n xs).digits.length=n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp only [run,List.length_cons,ih]

theorem trace_constant (n : Nat) (xs : List Nat) :
    (run n xs).events=plan n xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    simp only [run,ih,PV_L2E_DivisionTrace.trace_constant,
      PV_L2E_DivisionTrace.complete_value,pass_length,plan]

theorem bounds (n : Nat) (xs : List Nat) (hx : ∀ x∈xs,x<B) :
    (∀ x∈(run n xs).quotient,x<B) ∧ (∀ d∈(run n xs).digits,d<P) := by
  induction n generalizing xs with
  | zero => exact ⟨hx,by simp [run]⟩
  | succ n ih =>
    have hp := PV_L2E_DivisionTrace.safe 0 xs (by decide) hx
    have ht := ih _ hp.1
    refine ⟨ht.1,?_⟩
    intro d hd
    simp only [run,List.mem_cons] at hd
    rcases hd with rfl|hd
    · exact hp.2
    · exact ht.2 d hd

/-- No concrete large numeral or recurrence is normalized here. -/
theorem eight_word_trace (n : Nat) (xs : List Nat) (width : xs.length=8) :
    (run n xs).events=plan n 8 := by rw [trace_constant,width]

#print axioms quotient_length
#print axioms digit_count
#print axioms trace_constant
#print axioms bounds
#print axioms eight_word_trace
end PV_L2E_DigitsTrace
