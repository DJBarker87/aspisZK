import R1Z.ProverRwP6BodyData
import R1Z.PV_CB_Op114Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_StateChanged
open Aeneas Aeneas.Std Result ProverRwFull
attribute [local instance] Classical.propDecidable
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
/-- The current source checks fingerprints before byte arrays; both array
comparisons are already proved total. This is a Result law, not a trace law. -/
theorem source_status (a b : Context) :
    PV_CB_ShippedOp114.aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq a b =
      .ok (decide (a=b)) := by
  unfold PV_CB_ShippedOp114.aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq
  simp only [ProverRwSuccessByteEquality.array_eq,bind_tc_ok]
  cases a with
  | mk d n m l => cases b with
    | mk d' n' m' l' =>
      by_cases hd : d=d' <;> by_cases hn : n=n' <;>
      by_cases hm : m=m' <;> by_cases hl : l=l' <;>
        simp [hd,hn,hm,hl]
variable [ExternalTypes]
theorem selected_bridge (ops : ExternalFuns) (a b : Context) :
    (ProverRwP6BodyStore.selected ops).op114 a b = (PV_CB_Op114Source.selected ops).op114 a b :=
  (ProverRwSuccessEquality.context_total ops a b).trans
    ((source_status a b).symm.trans (PV_CB_Op114Source.op114_source ops a b).symm)
theorem op114_source (ops : ExternalFuns) (a b : Context) :
    (ProverRwP6BodyStore.selected ops).op114 a b =
      PV_CB_ShippedOp114.aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq a b :=
  (selected_bridge ops a b).trans (PV_CB_Op114Source.op114_source ops a b)
#print axioms source_status
#print axioms selected_bridge
#print axioms op114_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_StateChanged
