import R0P.SemDecision
/-! Small symbolic product lemmas for the terminal equality factor. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitTerminalMath51
open scoped BigOperators
variable {K : Type} [Field K]

def factor (a b : K) : K := 1-a-b+a*b+a*b

def product (a b : Nat → K) : Nat → Nat → K
 | 0,_ => 1
 | n+1,start => factor (a start) (b start)*product a b n (start+1)

theorem product_range (a b : Nat → K) (n start : Nat) :
    product a b n start=∏ j ∈ Finset.range n, factor (a (start+j)) (b (start+j)) := by
  induction n generalizing start with
  | zero => simp only [product,Finset.range_zero,Finset.prod_empty]
  | succ n ih =>
    rw [product,ih,Finset.prod_range_succ']
    simp only [Nat.add_zero]
    rw [mul_comm (factor (a start) (b start))]
    apply congrArg (fun x => x*factor (a start) (b start))
    apply Finset.prod_congr rfl
    intro j hj
    congr 2 <;> omega

theorem product_model [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (a b : Nat → K) : product a b 10 0=
      R0P.SemSource.eqValue (fun i : Fin 10 => a i.val) (fun i : Fin 10 => b i.val) := by
  rw [product_range]
  unfold R0P.SemSource.eqValue
  exact (Fin.prod_univ_eq_prod_range (fun j => factor (a j) (b j)) 10).symm

#print axioms product_range
#print axioms product_model
end R1Z.ProverCommitTerminalMath51
