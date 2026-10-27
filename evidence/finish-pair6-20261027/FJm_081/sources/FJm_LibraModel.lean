import FJg_DualTensor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraModel
open scoped BigOperators
variable {E : Type} [Field E]

def raw (q0 q1 : E) (j : Fin 1024) : E :=
  if j.val<28 then q0^j.val else if j.val<56 then q1^(j.val-28) else 0

def low (q a : E) : E := FJg_DualTensor.low (fun t=>q^t.val) a

def term (q a : E) (s : Fin 4) : E :=
  RoundPairing.quarter*q^(4*s.val)*a^((4-s.val)%4)

def part (q0 q1 a0 a1 : E) (i : Fin 4) : E :=
  match i.val with
  | 0=>low q0 a0*(term q0 a1 0+term q0 a1 1+term q0 a1 2+term q0 a1 3)
  | 1=>low q0 a0*(term q0 a1 0+term q0 a1 1+term q0 a1 2)*q0^16+
      low q1 a0*(RoundPairing.quarter*a1)
  | 2=>low q1 a0*(term q1 a1 0+term q1 a1 1+term q1 a1 2+term q1 a1 3)*q1^4
  | _=>low q1 a0*(term q1 a1 0+term q1 a1 1)*q1^20

def folded (q0 q1 a0 a1 : E) : Fin 64 → E :=
  RoundPairing.dualFold (n:=64) a1 (RoundPairing.dualFold (n:=256) a0 (raw q0 q1))

theorem support (q0 q1 a0 a1 : E) (i : Fin 64) (hi : 4 ≤ i.val) :
    folded q0 q1 a0 a1 i=0 := by
  unfold folded RoundPairing.dualFold
  have zero (s t : Fin 4) : raw q0 q1 (childIndex (childIndex i s) t)=0 := by
    have h : 56 ≤ (childIndex (childIndex i s) t).val := by
      dsimp only [childIndex]
      omega
    simp only [raw,if_neg (by omega : ¬(childIndex (childIndex i s) t).val<28),
      if_neg (by omega : ¬(childIndex (childIndex i s) t).val<56)]
  simp only [zero,zero_mul,Finset.sum_const_zero,mul_zero]

theorem small (q0 q1 a0 a1 : E) (i : Fin 4) :
    folded q0 q1 a0 a1 ⟨i.val,by have := i.isLt;omega⟩=part q0 q1 a0 a1 i := by
  fin_cases i <;>
    simp [folded,RoundPairing.dualFold,childIndex,raw,part,low,FJg_DualTensor.low,term,
      Fin.sum_univ_succ] <;> ring
#print axioms support
#print axioms small
end AspisR1.FJm_LibraModel
end
