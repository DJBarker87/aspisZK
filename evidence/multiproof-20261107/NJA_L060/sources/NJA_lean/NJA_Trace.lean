import Aeneas

set_option autoImplicit false
namespace NJA_Trace
inductive Kind where
 | initial (i : Nat)
 | internal (i : Nat)
 | final (i : Nat)
 deriving DecidableEq

def kind (n : Nat) : Kind :=
 if n < 4 then .initial n else if n < 18 then .internal (n-4) else .final (n-18)

structure Event (S : Type) where
 round : Nat
 kind : Kind
 input : S
 output : S
 deriving DecidableEq

-- Leading external is applied before the first round, but the first event's
-- input is the original raw input, as in the frozen caller.
def state {S : Type} (leading : S → S) (step : Nat → S → S) (initial : S) : Nat → S
 | 0 => leading initial
 | n+1 => step n (state leading step initial n)

def event {S : Type} (leading : S → S) (step : Nat → S → S) (initial : S) (n : Nat) : Event S :=
 ⟨n,kind n,if n=0 then initial else state leading step initial n,
   state leading step initial (n+1)⟩

def run {S : Type} (leading : S → S) (step : Nat → S → S) (initial : S) : Nat → List (Event S)
 | 0 => []
 | n+1 => run leading step initial n ++ [event leading step initial n]

theorem length {S : Type} (leading : S → S) (step : Nat → S → S) (initial : S) (n : Nat) :
 (run leading step initial n).length = n := by
 induction n with
 | zero => rfl
 | succ n ih => simp [run,ih]

theorem get {S : Type} (leading : S → S) (step : Nat → S → S) (initial : S)
 (n i : Nat) (hi : i<n) :
 (run leading step initial n)[i]'(by rw [length];exact hi) = event leading step initial i := by
 induction n with
 | zero => omega
 | succ n ih =>
   by_cases h : i<n
   · simp only [run,List.getElem_append_left (by rw [length];exact h)]
     exact ih h
   · have eq : i=n := by omega
     subst i
     simp [run,List.getElem_append_right,length]

theorem first_input {S : Type} (leading : S → S) (step : Nat → S → S) (initial : S) :
 (event leading step initial 0).input = initial := by simp [event]

theorem chronological {S : Type} (leading : S → S) (step : Nat → S → S) (initial : S) (n : Nat) :
 (event leading step initial (n+1)).input = (event leading step initial n).output := by simp [event]

theorem classes (n : Nat) (hn : n<22) :
 (n<4 ∧ kind n = .initial n) ∨
 (4≤n ∧ n<18 ∧ kind n = .internal (n-4)) ∨
 (18≤n ∧ kind n = .final (n-18)) := by
 by_cases a : n<4
 · exact Or.inl ⟨a,by simp [kind,a]⟩
 · by_cases b : n<18
   · exact Or.inr (Or.inl ⟨by omega,b,by simp [kind,a,b]⟩)
   · exact Or.inr (Or.inr ⟨by omega,by simp [kind,a,b]⟩)

#print axioms length
#print axioms get
#print axioms first_input
#print axioms chronological
#print axioms classes
end NJA_Trace
