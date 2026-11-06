import NKO_C02Source
set_option autoImplicit false
noncomputable section
namespace NKO_C02
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Domain of the SAME gamma at the actual powers event, internally derived. -/
theorem at_actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (gamma : aspis_core.field.wide_exact.WideExact)
 (reply : Result (Array aspis_core.field.wide_exact.WideExact 29#usize))
 (entered : Event.powers gamma reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 ∃ p a,NJJ_Common.resume wr d ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
 gamma=p.gamma ∧ NID_ResumeFields.Domain p a ∧
 NFN_LPi_FieldValues.canonE (FIo_Install.toE gamma) := by
 obtain ⟨p,a,resume,same,fields⟩ := source wr rr merkle finish d pub proof ck hash _ entered
 refine ⟨p,a,resume,same,fields,?_⟩
 rw [same]
 exact NID_ResumeCallerDomain.gamma p.gamma fields.gamma
#print at_actual
#print axioms at_actual
end NKO_C02
