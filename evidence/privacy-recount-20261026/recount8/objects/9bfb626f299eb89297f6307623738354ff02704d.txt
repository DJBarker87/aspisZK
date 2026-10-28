import R1Z.PV_RunJoin_AccLoop38
import R1Z.ProverCommitInterpolationRow48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AccPolynomial38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35
open ProverCommitInterpolationEmbed48 (embed)
variable [ExternalTypes]

def poly (p : Nat → Q) := ProverCommitInterpolationRow48.qpoly (fun k => old (p k))

/-- Complete current-source accumulator and its independent polynomial image.
No interpolation result or desired coefficient image occurs as a hypothesis. -/
theorem complete (ops : ExternalFuns) (p : Nat → Q) (basis : Nat → U32) (scale : Q)
    (hp : ∀ j, j<28 → canonical (p j)) :
    ∃ out : Nat → Q,
      @host_sumcheck.interpolation_accumulate _ (ProverRwP6BodyCandidate.selected ops)
        (array p) (ProverCommitM31Array48.array 28#usize basis) scale = .ok (array out) ∧
      (∀ j, j<28 → canonical (out j)) ∧
      poly out=poly p+Polynomial.C (value scale)*(ProverCommitBasisPolynomial48.poly basis).map embed := by
  obtain ⟨out,hout,hcan,hval⟩ := PV_RunJoin_AccLoop38.complete ops 28 0#usize p basis scale rfl hp
  refine ⟨out,hout,hcan,?_⟩
  have hv : ∀ k, k<28 → value (out k)=value (p k)+value scale*embed (ProverCommitM31Ops48.decode (basis k)) := by
    intro k hk
    rw [hval k hk,if_pos (by change 0≤k ∧ k<0+28;omega),ProverCommitInterpolationEmbed48.source_embed]
  apply Polynomial.ext
  intro k
  simp only [poly,ProverCommitInterpolationRow48.qpoly,ProverCommitBasisPolynomial48.poly,
    Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_map,ProverCommitInterpolationPoly48.coeff]
  by_cases hk : k<28
  · simp only [if_pos hk]
    exact hv k hk
  · simp only [if_neg hk,map_zero,mul_zero,add_zero]

#print axioms complete
end R1Z.PV_RunJoin_AccPolynomial38
