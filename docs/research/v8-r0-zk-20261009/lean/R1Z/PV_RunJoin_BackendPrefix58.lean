import R1Z.PV_RunJoin_BackendMatrix58
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendPrefix58
open ProverRwFull PV_RunJoin_BackendMatrix58

def filled (p : Nat → Nat → W) (lane : Nat) (target : Nat → W) (stop : Nat) : Nat → Nat → W :=
  Function.update p lane (fun j => if j<stop then target j else p lane j)

theorem zero (p : Nat → Nat → W) (lane : Nat) (target : Nat → W) :
    filled p lane target 0=p := by
  funext l j
  by_cases hl : l=lane
  · subst l
    simp only [filled,Function.update_self,Nat.not_lt_zero,if_false]
  · simp only [filled,Function.update_of_ne hl]

theorem step (p : Nat → Nat → W) (lane row : Nat) (target : Nat → W) :
    Function.update (filled p lane target row) lane
      (Function.update ((filled p lane target row) lane) row (target row))=
      filled p lane target (row+1) := by
  funext l j
  by_cases hl : l=lane
  · subst l
    simp only [filled,Function.update_self]
    by_cases hj : j=row
    · subst j
      simp only [Function.update_self,Nat.lt_succ_self,if_true]
    · simp only [Function.update_of_ne hj]
      have he : (j<row)=(j<row+1) := propext (by omega)
      rw [he]
  · simp only [filled,Function.update_of_ne hl]

theorem full (p : Nat → Nat → W) (lane : Nat) (target : Nat → W) (l j : Nat) (hj : j<1024) :
    filled p lane target 1024 l j=(if l=lane then target j else p l j) := by
  by_cases hl : l=lane
  · subst l
    simp only [filled,Function.update_self,hj,if_true]
  · simp only [filled,Function.update_of_ne hl,hl,if_false]

#print axioms zero
#print axioms step
#print axioms full
end R1Z.PV_RunJoin_BackendPrefix58
