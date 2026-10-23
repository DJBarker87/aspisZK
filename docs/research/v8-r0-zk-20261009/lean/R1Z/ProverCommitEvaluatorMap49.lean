import R1Z.ProverCommitWeightMap49
/-! Generic evaluator transport, avoiding concrete tower-instance conversion
inside the seven-row composition. Every sum/product stays symbolic. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEvaluatorMap49
open ProverCommitEval47 AspisCircleTensorBinding
open scoped BigOperators
variable {K L : Type} [Field K] [Field L]

theorem doubled_map (f : K →+* L) (x : K) (n : Nat) :
    f (doubledFactor x n)=doubledFactor (f x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [doubledFactor,map_sub,map_mul,map_pow,map_ofNat,map_one,ih]

theorem natural_map (f : K →+* L) (x : K) (n : Nat) :
    f (naturalLineValue x n)=naturalLineValue (f x) n := by
  unfold naturalLineValue
  simp only [map_prod,doubled_map]

theorem message_map (f : K →+* L) (q : Fin 1024 → K) (x y : K) :
    f (messageEval q x y)=messageEval (fun i => f (q i)) (f x) (f y) := by
  unfold messageEval pairEval
  simp only [map_add,map_sum,map_mul,natural_map]

theorem single_map (f : K →+* L) (j : Fin 1024) :
    (fun i => f ((Pi.single j 1 : Fin 1024 → K) i))=(Pi.single j 1 : Fin 1024 → L) := by
  funext i
  by_cases h : i=j
  · subst i;simp only [Pi.single_eq_same,map_one]
  · simp only [Pi.single_eq_of_ne h,map_zero]

theorem message_single_map (f : K →+* L) (j : Fin 1024) (x y : K) :
    f (messageEval (Pi.single j 1) x y)=messageEval (Pi.single j 1) (f x) (f y) := by
  rw [message_map,single_map]

#print axioms doubled_map
#print axioms natural_map
#print axioms message_map
#print axioms single_map
#print axioms message_single_map
end R1Z.ProverCommitEvaluatorMap49
