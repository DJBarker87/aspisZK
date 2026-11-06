import NJA_External

set_option autoImplicit false
namespace NJA_Sums

def sum (f : Nat → Nat) : Nat → Nat
 | 0 => 0
 | n+1 => sum f n + f n

theorem replay (f states : Nat → Nat) (start : states 0=0)
 (step : ∀ n, states (n+1)=states n+f n) (n : Nat) : states n = sum f n := by
 induction n with
 | zero => exact start
 | succ n ih => rw [step,ih,sum]

theorem bound (f : Nat → Nat) (b n : Nat) (words : ∀ i<n, f i≤b) :
 sum f n ≤ n*b := by
 induction n with
 | zero => simp [sum]
 | succ n ih =>
   have prev := ih (by intro i hi;exact words i (by omega))
   have last := words n (by omega)
   simp only [sum,Nat.add_mul,Nat.one_mul]
   omega

theorem range_fold (f : Nat → Nat) (n : Nat) :
 sum f n = (List.range n).foldl (fun s i => s+f i) 0 := by
 induction n with
 | zero => rfl
 | succ n ih => simp [sum,List.range_succ,List.foldl_append,ih]

theorem four (f : Nat → Nat) : sum f 4 = (((0+f 0)+f 1)+f 2)+f 3 := rfl

#print axioms replay
#print axioms bound
#print axioms range_fold
#print axioms four
end NJA_Sums
