import R1Z.PV_RDCD_V216Raw
import R1Z.PV_RDCD_ByteArray
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD_ContextTotal
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev Context := PV_RDCD_V216.aspis_core.state_only_hiding.StateOnlyHidingContext
/-- Full Result on every context, with no library-law hypothesis. -/
theorem total (a b : Context) :
    PV_RDCD_V216.context_eq a b = ok (decide (a=b)) := by
  unfold PV_RDCD_V216.context_eq
    PV_RDCD_V216.aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq
  simp only [PV_RDCD_ByteArray.array_eq, bind_tc_ok]
  cases a with
  | mk d n m l => cases b with
    | mk d' n' m' l' =>
      by_cases hd : d=d' <;> by_cases hn : n=n' <;>
      by_cases hm : m=m' <;> by_cases hl : l=l' <;>
        simp [hd,hn,hm,hl]
#print axioms total
end R1Z.PV_RDCD_ContextTotal
