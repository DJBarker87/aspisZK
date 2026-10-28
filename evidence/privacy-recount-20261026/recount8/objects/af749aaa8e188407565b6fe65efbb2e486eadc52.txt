import R1Z.PV_Join_InterpolateStepCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_InterpolateCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5 PV_Join_ResultInvariant5
open PV_Join_AccumulateCanonical5
variable [ExternalTypes]

theorem loop (ops : ExternalFuns) (values out : QA) (i : Usize) (hout : QArray out) :
    Safe QArray (@host_sumcheck.interpolate_loop _ (ProverRwP6BodyStore.selected ops) values out i) := by
  unfold host_sumcheck.interpolate_loop
  exact PV_Join_LoopInvariant5.preserve rank inv QArray
    (fun s => @host_sumcheck.interpolate_loop.body _ (ProverRwP6BodyStore.selected ops) values s.1 s.2)
    (by
      rintro ⟨ys,j⟩ hys cf hcf
      cases cf with
      | done z => exact PV_Join_InterpolateStepCanonical5.step ops values ys j hys (.done z) hcf
      | cont z => exact PV_Join_InterpolateStepCanonical5.step ops values ys j hys (.cont z) hcf)
    (out,i) hout

theorem interpolate (ops : ExternalFuns) (values : QA) :
    Safe QArray (@host_sumcheck.interpolate _ (ProverRwP6BodyStore.selected ops) values) := by
  unfold host_sumcheck.interpolate
  change Safe QArray (do
    let q ← Result.ok (ProverRwDictionaryTower.fromQ AspisR1ProducerRelease47.field.QM31.ZERO)
    @host_sumcheck.interpolate_loop _ (ProverRwP6BodyStore.selected ops) values (Array.repeat 28#usize q) 0#usize)
  rw [AspisR1ProducerRelease47.field.QM31.ZERO]
  simp only [bind_tc_ok]
  change Safe QArray (@host_sumcheck.interpolate_loop _ (ProverRwP6BodyStore.selected ops)
    values (Array.repeat 28#usize ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩) 0#usize)
  exact loop ops values _ _ (PV_Join_CanonicalArray5.array_repeat _ q_zero)

#print axioms loop
#print axioms interpolate
end R1Z.PV_Join_InterpolateCanonical5
