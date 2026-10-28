import R1Z.PV_Join_GAccumulateCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_GAccumulateLoopCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5 PV_Join_ResultInvariant5
open PV_Join_GAccumulateCanonical5
variable [ExternalTypes]

theorem loop (dict : ExternalFuns) (laws : PV_Join_CanonicalPrimitives5.Laws dict) (out : QA) (basis : MA)
    (scale : aspis_core.field.QM31) (k : Usize) (hout : QArray out) :
    Safe QArray (@host_sumcheck.interpolation_accumulate_loop _
      dict out basis scale k) := by
  unfold host_sumcheck.interpolation_accumulate_loop
  exact PV_Join_LoopInvariant5.preserve rank inv QArray
    (fun s => @host_sumcheck.interpolation_accumulate_loop.body _
      dict basis scale s.1 s.2)
    (by
      rintro ⟨ys,i⟩ hys cf hcf
      cases cf with
      | done z => exact step dict laws basis scale ys i hys (.done z) hcf
      | cont z => exact step dict laws basis scale ys i hys (.cont z) hcf)
    (out,k) hout

theorem accumulate (dict : ExternalFuns) (laws : PV_Join_CanonicalPrimitives5.Laws dict) (out : QA) (basis : MA)
    (scale : aspis_core.field.QM31) (hout : QArray out) :
    Safe QArray (@host_sumcheck.interpolation_accumulate _
      dict out basis scale) :=
  loop dict laws out basis scale 0#usize hout

#print axioms loop
#print axioms accumulate
end R1Z.PV_Join_GAccumulateLoopCanonical5
