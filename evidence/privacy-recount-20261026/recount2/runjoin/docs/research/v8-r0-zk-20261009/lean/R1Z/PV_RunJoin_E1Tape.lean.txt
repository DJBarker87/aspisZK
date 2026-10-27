import R1Z.ProverCommitPublicNonce40
import R1Z.CouplingR1PBin
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_E1Tape
open R0Z R0Z.FsStatement ProverCommitPublicNonce40

/-- Completion of successful-return coins only. Failed calls have no invented
availability law. `context` may depend on the entire completed private tape;
E1 is pointwise in complete prior context, so no independence is smuggled into
this algebraic identity. Native adaptedness/association stays V336/V339. -/
def weight {C : Type} (law : C → Raw → ℚ) (n : Nat)
    (context : Fin n → (Fin n → Raw) → C) (t : Fin n → Raw) : ℚ :=
  ∏ i, law (context i t) (t i)

theorem weight_uniform {C : Type} (law : C → Raw → ℚ) (e1 : E1 law)
    (n : Nat) (context : Fin n → (Fin n → Raw) → C) (t : Fin n → Raw) :
    weight law n context t = 1 / (Fintype.card (Fin n → Raw) : ℚ) := by
  unfold weight
  unfold ProverCommitPublicNonce40.E1 at e1
  simp only [e1,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Fintype.card_fun,Nat.cast_pow,one_div_pow]

theorem completed_mean {C : Type} (law : C → Raw → ℚ) (e1 : E1 law)
    (n : Nat) (context : Fin n → (Fin n → Raw) → C) (f : (Fin n → Raw) → ℚ) :
    (∑ t, weight law n context t * f t) = mean f := by
  simp only [weight_uniform law e1,one_div_mul_eq_div,← Finset.sum_div,mean]

/-- Push-forward to another finite carrier needs its own checked coordinate
law. E1 alone supplies the successful raw tape law, not an arbitrary model map. -/
theorem mapped_mean {C M : Type} [Fintype M]
    (law : C → Raw → ℚ) (e1 : E1 law) (n : Nat)
    (context : Fin n → (Fin n → Raw) → C) (coordinates : (Fin n → Raw) → M)
    (coordinate_law : ∀ f : M → ℚ, mean (fun t => f (coordinates t)) = mean f)
    (f : M → ℚ) :
    (∑ t, weight law n context t * f (coordinates t)) = mean f := by
  rw [completed_mean law e1]
  exact coordinate_law f

#print axioms weight_uniform
#print axioms completed_mean
#print axioms mapped_mean
end R1Z.PV_RunJoin_E1Tape
