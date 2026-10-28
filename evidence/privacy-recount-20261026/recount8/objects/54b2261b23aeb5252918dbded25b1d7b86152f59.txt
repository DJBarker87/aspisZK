import R1Z.PV_RunJoin_ScalarSource38
import R1Z.PV_RunJoin_MergeArray35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AccStep38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FieldData34 PV_RunJoin_MergeArray35
variable [ExternalTypes]

theorem stop (ops : ExternalFuns) (out : Array Q 28#usize)
    (basis : Array U32 28#usize) (scale : Q) (k : Usize) (hk : ¬k.val<28) :
    @host_sumcheck.interpolation_accumulate_loop.body _ (ProverRwP6BodyCandidate.selected ops)
      basis scale out k = .ok (.done out) := by
  simp only [host_sumcheck.interpolation_accumulate_loop.body,
    show ¬k<28#usize from hk,↓reduceIte]

theorem step (ops : ExternalFuns) (p : Nat → Q) (basis : Nat → U32)
    (scale : Q) (k : Usize) (hk : k.val<28)
    (hp : ∀ j, j<28 → canonical (p j)) :
    ∃ z,
      @host_sumcheck.interpolation_accumulate_loop.body _ (ProverRwP6BodyCandidate.selected ops)
        (ProverCommitArray49.array 28#usize basis) scale (array p) k =
        .ok (.cont (array (Function.update p k.val z),Usize.wrapping_add k 1#usize)) ∧
      canonical z ∧ value z = value (p k.val)+value scale*ProverCommitScalar48.embed (basis k.val) := by
  obtain ⟨delta,hdelta,hcd,hvd⟩ := PV_RunJoin_ScalarSource38.complete ops scale (basis k.val)
  obtain ⟨z,hz,hcz,hvz⟩ := PV_RunJoin_FieldData34.add ops (p k.val) delta (hp _ hk) hcd
  have hsum : @aspis_core.field.QM31.add _ (ProverRwP6BodyCandidate.selected ops)
      (p k.val) delta = .ok z := hz
  refine ⟨z,?_,hcz,by rw [hvz,hvd]⟩
  unfold host_sumcheck.interpolation_accumulate_loop.body
  simp only [show k<28#usize from hk,↓reduceIte]
  rw [read p k hk]
  simp only [bind_tc_ok]
  rw [ProverCommitArray49.index 28#usize basis k hk]
  simp only [bind_tc_ok,hdelta,hsum]
  rw [write p k hk z]
  simp only [bind_tc_ok,lift]

#print axioms stop
#print axioms step
end R1Z.PV_RunJoin_AccStep38
