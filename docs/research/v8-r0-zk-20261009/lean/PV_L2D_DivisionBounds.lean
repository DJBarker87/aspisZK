import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_DivisionBounds
abbrev P : Nat := 2147483647
abbrev B : Nat := 4294967296

def dividend (remainder limb : Nat) := remainder*B+limb

theorem dividend_bound (r x : Nat) (hr : r<P) (hx : x<B) :
    dividend r x<P*B := by
  norm_num only [dividend,P,B] at *
  omega
#print axioms dividend_bound

theorem u64_safe (r x : Nat) (hr : r<P) (hx : x<B) :
    dividend r x<2^63 ∧ dividend r x<2^64 := by
  have h:=dividend_bound r x hr hx
  norm_num only [P,B] at h
  omega
#print axioms u64_safe

theorem quotient_word (r x : Nat) (hr : r<P) (hx : x<B) :
    dividend r x / P<B := by
  exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [Nat.mul_comm] using dividend_bound r x hr hx)
#print axioms quotient_word

theorem remainder_field (r x : Nat) : dividend r x % P<P := Nat.mod_lt _ (by decide)
#print axioms remainder_field

structure Step where
  quotient : Nat
  remainder : Nat

def step (r x : Nat) : Step := ⟨dividend r x/P,dividend r x%P⟩

theorem step_total (r x : Nat) (hr : r<P) (hx : x<B) :
    (step r x).quotient<B ∧ (step r x).remainder<P ∧
    dividend r x<2^64 :=
  ⟨quotient_word r x hr hx,remainder_field r x,(u64_safe r x hr hx).2⟩
#print axioms step_total

/-- The source's reverse 8-limb pass. Each returned quotient is the new
word, not the old word: no mutable-borrow restoration is abstracted away. -/
def pass : Nat → List Nat → List Nat × Nat
  | r,[] => ([],r)
  | r,x::xs =>
    let d:=step r x
    let tail:=pass d.remainder xs
    (d.quotient::tail.1,tail.2)

theorem pass_length (r : Nat) (xs : List Nat) : (pass r xs).1.length=xs.length := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => simp [pass,ih]
#print axioms pass_length

theorem pass_bounds (r : Nat) (xs : List Nat) (hr : r<P) (hx : ∀ x∈xs,x<B) :
    (∀ y∈(pass r xs).1,y<B) ∧ (pass r xs).2<P := by
  induction xs generalizing r with
  | nil => exact ⟨by simp [pass],hr⟩
  | cons x xs ih =>
    have s:=step_total r x hr (hx x (by simp))
    have t:=ih (step r x).remainder s.2.1 (fun y hy=>hx y (by simp [hy]))
    constructor
    · intro y hy
      simp only [pass,List.mem_cons] at hy
      rcases hy with rfl|hy
      · exact s.1
      · exact t.1 y hy
    · exact t.2
#print axioms pass_bounds

/-- The native dividend decomposition is lossless at every word. -/
theorem step_reconstruct (r x : Nat) :
    (step r x).quotient*P+(step r x).remainder=dividend r x := by
  simpa only [step,Nat.mul_comm] using Nat.div_add_mod (dividend r x) P
#print axioms step_reconstruct
end PV_L2D_DivisionBounds
