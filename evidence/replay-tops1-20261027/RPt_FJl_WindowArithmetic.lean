import Mathlib.Tactic
set_option autoImplicit false
namespace AspisR1.FJl_WindowArithmetic
/-- Symbolic fixed-layout slice compositions; only small offset arithmetic. -/
theorem scalar {A : Type} (bs : List A) (s l : Nat) (hs : s<4) (hl : l<26) :
    (((((bs.take 480).drop (120*s)).take 120).take 104).drop (4*l)).take 4=
      (bs.drop (120*s+4*l)).take 4 := by
  simp only [List.drop_take,List.take_take,List.drop_drop]
  congr 1 <;> omega

theorem c1tail {A : Type} (bs : List A) (s : Nat) (hs : s<4) :
    (((bs.take 480).drop (120*s)).take 120).drop 104=
      (bs.drop (120*s+104)).take 16 := by
  simp only [List.drop_take,List.take_take,List.drop_drop]
  congr 1 <;> omega

theorem c2 {A : Type} (bs : List A) (s l : Nat) (hs : s<4) (hl : l<2) :
    (((((bs.drop 480).take 128).drop (32*s)).take 32).drop (16*l)).take 16=
      (bs.drop (480+32*s+16*l)).take 16 := by
  simp only [List.drop_take,List.take_take,List.drop_drop]
  congr 1 <;> omega
#print axioms scalar
#print axioms c1tail
#print axioms c2
end AspisR1.FJl_WindowArithmetic
