import R1Z.PV_RunJoin_BasisInitial38
import R1Z.PV_RunJoin_AccPolynomial38
import R1Z.ProverCommitInterpolationOutput48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InterpolationRow38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35 PV_RunJoin_AccPolynomial38
variable [ExternalTypes]

theorem stop (ops : ExternalFuns) (values out : Array Q 28#usize) (i : Usize) (hi : ¬i.val<28) :
    @host_sumcheck.interpolate_loop.body _ (ProverRwP6BodyCandidate.selected ops) values out i =
      .ok (.done out) := by
  simp only [host_sumcheck.interpolate_loop.body,show ¬i<28#usize from hi,↓reduceIte]

/-- A complete actual interpolation row: all basis factors, a proved nonzero
inverse, raw-value scaling and all 28 output coefficients are discharged. -/
theorem step (ops : ExternalFuns) (values p : Nat → Q) (i : Usize) (hi : i.val<28)
    (hp : ∀ k, k<28 → canonical (p k)) :
    ∃ out : Nat → Q,
      @host_sumcheck.interpolate_loop.body _ (ProverRwP6BodyCandidate.selected ops)
        (array values) (array p) i =
        .ok (.cont (array out,Usize.wrapping_add i 1#usize)) ∧
      (∀ k, k<28 → canonical (out k)) ∧
      poly out=poly p+ProverCommitInterpolationOutput48.contribution (old (values i.val)) i.val := by
  obtain ⟨basis,den,hbasis,hcb,hcd,hpoly,hdd,hn⟩ := PV_RunJoin_BasisInitial38.complete ops i hi
  obtain ⟨inv,hinv,hcinv,hdinv⟩ := ProverCommitInterpolationInverse48.inverse_exact den hn
  have inverse : @aspis_core.field.M31.inv _ (ProverRwP6BodyCandidate.selected ops) den=.ok inv := hinv
  obtain ⟨scale,hscale,hcscale,hdscale⟩ := PV_RunJoin_ScalarSource38.complete ops (values i.val) inv
  obtain ⟨out,hout,hcan,hacc⟩ := PV_RunJoin_AccPolynomial38.complete ops p basis scale hp
  refine ⟨out,?_,hcan,?_⟩
  · unfold host_sumcheck.interpolate_loop.body
    simp only [show i<28#usize from hi,↓reduceIte,hbasis,bind_tc_ok]
    rw [read values i hi]
    change (do
      let m ← @aspis_core.field.M31.inv _ (ProverRwP6BodyCandidate.selected ops) den
      let scale ← @aspis_core.field.QM31.mul_m31 _ (ProverRwP6BodyCandidate.selected ops) (values i.val) m
      let out1 ← @host_sumcheck.interpolation_accumulate _ (ProverRwP6BodyCandidate.selected ops)
        (array p) (ProverCommitM31Array48.array 28#usize basis) scale
      Result.ok (ControlFlow.cont (out1,Usize.wrapping_add i 1#usize) :
        ControlFlow ((Array Q 28#usize) × Usize) (Array Q 28#usize))) = _
    simp only [bind_tc_ok,inverse,hscale,hout,lift]
  · change ProverCommitM31Ops48.decode inv=(ProverCommitM31Ops48.decode den)⁻¹ at hdinv
    rw [hacc,hdscale,ProverCommitInterpolationEmbed48.source_embed,hdinv,hdd,hpoly]
    rfl

#print axioms stop
#print axioms step
end R1Z.PV_RunJoin_InterpolationRow38
