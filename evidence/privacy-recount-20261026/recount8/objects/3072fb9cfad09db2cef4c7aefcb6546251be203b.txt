import R1Z.PV_Join_GInterpolateStepCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_GInterpolateCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5 PV_Join_ResultInvariant5
open PV_Join_GAccumulateCanonical5
variable [ExternalTypes]

theorem loop (dict : ExternalFuns) (laws : PV_Join_CanonicalPrimitives5.Laws dict) (values out : QA) (i : Usize) (hout : QArray out) :
    Safe QArray (@host_sumcheck.interpolate_loop _ dict values out i) := by
  unfold host_sumcheck.interpolate_loop
  exact PV_Join_LoopInvariant5.preserve rank inv QArray
    (fun s => @host_sumcheck.interpolate_loop.body _ dict values s.1 s.2)
    (by
      rintro ⟨ys,j⟩ hys cf hcf
      cases cf with
      | done z => exact PV_Join_GInterpolateStepCanonical5.step dict laws values ys j hys (.done z) hcf
      | cont z => exact PV_Join_GInterpolateStepCanonical5.step dict laws values ys j hys (.cont z) hcf)
    (out,i) hout

theorem interpolate (dict : ExternalFuns) (laws : PV_Join_CanonicalPrimitives5.Laws dict) (values : QA) :
    Safe QArray (@host_sumcheck.interpolate _ dict values) := by
  unfold host_sumcheck.interpolate
  rw [show @aspis_core.field.QM31.ZERO _ dict = .ok ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ from laws.zero]
  simp only [bind_tc_ok]
  change Safe QArray (@host_sumcheck.interpolate_loop _ dict
    values (Array.repeat 28#usize ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩) 0#usize)
  exact loop dict laws values _ _ (PV_Join_CanonicalArray5.array_repeat _ q_zero)

#print axioms loop
#print axioms interpolate
end R1Z.PV_Join_GInterpolateCanonical5
