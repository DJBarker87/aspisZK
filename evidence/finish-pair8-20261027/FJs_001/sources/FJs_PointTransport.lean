import FJr_PairRows
import R1SelectedOpeningFunctionals
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_PointTransport
open scoped BigOperators
variable {K E : Type} [Field K] [Field E]

theorem tensor (h : K →+* E) (p : Fin 10 → K) (j : Fin 1024) :
    h (tensorPoint p j)=tensorPoint (fun i=>h (p i)) j := by
  unfold tensorPoint pairFactor
  simp only [map_prod,map_mul,map_sub,map_one,apply_ite]

theorem carry (h : K →+* E) (p : Fin 10 → K) (n : Nat) :
    h (R0P.SemSource.succCarry p n)=R0P.SemSource.succCarry (fun i=>h (p i)) n := by
  induction n with
  | zero=>exact h.map_one
  | succ n ih=>
    simp only [R0P.SemSource.succCarry,map_mul,ih]
    split <;> simp only [map_zero]

theorem successor (h : K →+* E) (p : Fin 10 → K) :
    (fun i=>h (R0P.SemSource.successorPoint p i))=
      R0P.SemSource.successorPoint (fun i=>h (p i)) := by
  funext i
  simp only [R0P.SemSource.successorPoint,map_sub,map_add,map_mul,carry]

theorem xor (h : K →+* E) (p : Fin 10 → K) :
    (fun i=>h (R0P.SemSource.xor12Point p i))=
      R0P.SemSource.xor12Point (fun i=>h (p i)) := by
  funext i
  unfold R0P.SemSource.xor12Point
  split <;> simp only [map_sub,map_one]

theorem libra (h : K →+* E) (p : Fin 10 → K) (j : Fin 1024) :
    h (FJm_LibraModel.raw (p 8) (p 9) j)=R0P.SemSource.libraWeight (fun i=>h (p i)) j := by
  unfold FJm_LibraModel.raw R0P.SemSource.libraWeight
  split <;> first | exact h.map_pow _ _ | skip
  split <;> simp only [map_pow,map_zero]

#print axioms tensor
#print axioms carry
#print axioms successor
#print axioms xor
#print axioms libra
end AspisR1.FJs_PointTransport
end
