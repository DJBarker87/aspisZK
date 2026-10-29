import R1Z.PV_RunJoin_BackendRepresentation58
import R1Z.PV_RunJoin_BackendPrefix58
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendBasePrefix58
open Aeneas Aeneas.Std ProverRwFull PV_RunJoin_BackendMatrix58

def bases (p input : Nat → Nat → W) (stop : Nat) (l j : Nat) : W :=
  if l<stop then input l j else p l j

theorem zero (p input : Nat → Nat → W) : bases p input 0=p := by
  funext l j
  simp only [bases,Nat.not_lt_zero,if_false]

theorem step (p input : Nat → Nat → W) (lane : Nat) :
    matrix (PV_RunJoin_BackendPrefix58.filled (bases p input lane) lane (input lane) 1024)=
      matrix (bases p input (lane+1)) := by
  apply PV_RunJoin_BackendRepresentation58.matrix_congr
  intro l hl j hj
  rw [PV_RunJoin_BackendPrefix58.full _ _ _ l j hj]
  by_cases he : l=lane
  · subst l
    simp only [if_true,bases,Nat.lt_succ_self]
  · simp only [if_neg he,bases]
    by_cases hb : l<lane
    · simp only [if_pos hb,if_pos (show l<lane+1 by omega)]
    · simp only [if_neg hb,if_neg (show ¬l<lane+1 by omega)]

#print axioms zero
#print axioms step
end R1Z.PV_RunJoin_BackendBasePrefix58
