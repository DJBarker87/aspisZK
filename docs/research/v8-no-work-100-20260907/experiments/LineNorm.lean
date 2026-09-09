import Mathlib.Tactic
namespace AspisV8.LineNorm
def p : Nat := 2147483647
-- Literal low31 rotate used by M31::half, expressed on natural representatives.
def halfWord (x : Nat) := (x >>> 1) ||| ((x &&& 1) <<< 30)
theorem half_arithmetic (x : Nat) (hx : x<p) :
    halfWord x = x/2+(x%2)*1073741824 := by
  dsimp [halfWord]
  rw [Nat.shiftRight_eq_div_pow,Nat.and_one_is_mod,Nat.shiftLeft_eq]
  norm_num
  have hbit : x%2=0 ∨ x%2=1 := by omega
  rcases hbit with h | h
  · simp [h]
  · simp only [h,one_mul]
    apply Nat.or_two_pow_eq_add_of_lt (n:=30)
    dsimp [p] at hx
    norm_num
    omega

theorem half_range_and_double (x : Nat) (hx : x<p) :
    halfWord x<p ∧ 2*halfWord x=x+(x%2)*p := by
  rw [half_arithmetic x hx]
  dsimp [p] at *
  have hm := Nat.mod_lt x (by decide : 0<2)
  have hd := Nat.mod_add_div x 2
  omega

theorem half_word_ranges (x : Nat) (hx : x<p) :
    x>>>1<2^32 ∧ (x&&&1)<<<30<2^32 ∧ halfWord x<2^32 := by
  have hh := (half_range_and_double x hx).1
  rw [Nat.shiftRight_eq_div_pow,Nat.and_one_is_mod,Nat.shiftLeft_eq]
  dsimp [p] at hx hh
  have hm := Nat.mod_lt x (by decide : 0<2)
  norm_num
  omega

theorem half_cast (x : Nat) (hx : x<p) :
    2*(halfWord x : ZMod p)=(x:ZMod p) := by
  have h := congrArg (fun n : Nat => (n : ZMod p)) (half_range_and_double x hx).2
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,ZMod.natCast_self,
    mul_zero,add_zero] using h

variable {R : Type*} [CommRing R]
def line (x : R) := 2*x^2-1
def four (e a b c : R) := ((e+a)+(b+c),(e+a)-(b+c),(e-a)-(b-c),(e-a)+(b-c))

theorem even_line (a b h x : R) (hh : 2*h=b) :
    (a+h)+h*line x=a+b*x^2 := by
  dsimp [line]
  linear_combination x^2*hh

theorem four_line (a b h x u v w : R) (hh : 2*h=b) :
    four ((a+h)+h*line x) u v w=four (a+b*x^2) u v w := by
  rw [even_line a b h x hh]

-- Loop invariant of the actual push-only coordinate buffer. It never takes
-- a prover-supplied coordinate and does not change the traversal order.
theorem coordinate_push_loop (points : List (R × R)) (acc : List R) :
    points.foldl (fun out p => out++[line p.1]) acc =
      acc++points.map (fun p => line p.1) := by
  induction points generalizing acc with
  | nil => simp
  | cons pt pts ih => simp [List.foldl_cons,ih,List.append_assoc]

theorem line_buffer_length (points : List (R × R)) :
    (points.map (fun p => line p.1)).length=points.length := by simp

-- CM31::half applies the same rotate independently to its two limbs.
theorem cm_half (embed : ZMod p →+* R) (imaginary : R)
    (a b : Nat) (ha : a<p) (hb : b<p) :
    2*(embed (halfWord a)+imaginary*embed (halfWord b)) =
      embed (a:ZMod p)+imaginary*embed (b:ZMod p) := by
  have hA := congrArg embed (half_cast a ha)
  have hB := congrArg embed (half_cast b hb)
  simp only [map_mul,map_ofNat] at hA hB
  linear_combination hA+imaginary*hB

theorem mismatched_line_counterexample :
    ((0:ℤ)+1)+1*0 ≠ 0+2*0^2 := by norm_num

#print axioms half_arithmetic
#print axioms half_range_and_double
#print axioms half_word_ranges
#print axioms half_cast
#print axioms even_line
#print axioms four_line
#print axioms coordinate_push_loop
#print axioms line_buffer_length
#print axioms cm_half
#print axioms mismatched_line_counterexample
end AspisV8.LineNorm
