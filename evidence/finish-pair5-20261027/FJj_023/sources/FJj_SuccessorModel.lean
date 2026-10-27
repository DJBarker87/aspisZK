import FJd_LoopReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorModel
variable {K : Type} [Field K]
def index (i : Nat) : Fin 10 := ⟨i%10,Nat.mod_lt _ (by decide)⟩
def eval (z : Fin 10 → K) (n : Nat) (state : K × (Fin 10 → K)) : K × (Fin 10 → K) :=
  ((List.range n).reverse).foldl (fun st i=>FJd_LoopReference.successorStep z st (index i)) state

theorem zero (z : Fin 10 → K) (state : K × (Fin 10 → K)) : eval z 0 state=state := rfl

theorem succ (z : Fin 10 → K) (n : Nat) (state : K × (Fin 10 → K)) :
    eval z (n+1) state=eval z n (FJd_LoopReference.successorStep z state (index n)) := by
  simp only [eval,List.range_succ,List.reverse_append,List.reverse_singleton,
    List.foldl_append,List.foldl_cons,List.foldl_nil]
#print axioms zero
#print axioms succ
end AspisR1.FJj_SuccessorModel
end
