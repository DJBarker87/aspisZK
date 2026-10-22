import R1Z.Batched
import R1Z.ProverCommitEval47
/-! Identification of all seven raw coefficient rows with the existing R1
functionals on basis vectors. Finite sums remain symbolic. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRawCoefficient49
open R0Z.HonestView R0P R0P.SemSource
open AspisR0.Opening AspisR0.ChordGeometry
open scoped BigOperators
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [NeZero (2 : K)]

def model (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (j : Fin 1024) : Fin 7 → K :=
  ![indicator copyInactiveRows (π.symm j),
    eqWeight (openingPoints (alpha ch) 0) (π.symm j),
    eqWeight (openingPoints (alpha ch) 1) (π.symm j),
    eqWeight (openingPoints (alpha ch) 2) (π.symm j),
    libraWeight (alpha ch) j,
    ProverCommitEval47.messageEval (Pi.single j 1) (ch.circle 0).1.1 (ch.circle 0).1.2,
    ProverCommitEval47.messageEval (Pi.single j 1) (ch.circle 1).1.1 (ch.circle 1).1.2]

theorem dot_single {N : Nat} (w : Fin N → K) (j : Fin N) :
    dotLinear w (Pi.single j 1)=w j := by
  rw [R1Z.Batched.dotLinear_apply]
  simp [Pi.single_apply,eq_comm]

attribute [local irreducible] dotLinear ProverCommitEval47.messageEval

theorem model_eq_ell (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (j : Fin 1024) (k : Fin 7) :
    model π ch j k=R1Z.Batched.ell π ch k (Pi.single j 1) := by
  fin_cases k <;> simp [model,R1Z.Batched.ell,dot_single,oodLinear_apply,
    ProverCommitEval47.message_model]

theorem weighted_model (π : Fin 1024 ≃ Fin 1024) (ch : Challenges K) (j : Fin 1024) :
    (∑ k : Fin 7, ch.opening 1^k.val*model π ch j k)=R1Z.Batched.weightsR1 π ch j := by
  simp only [model_eq_ell,R1Z.Batched.weightsR1,R1Z.BatchedAlgebra.weightsOf]

#print axioms dot_single
#print axioms model_eq_ell
#print axioms weighted_model
end R1Z.ProverCommitRawCoefficient49
