import LPq_SelectedDomain
set_option autoImplicit false
namespace AspisR1.LPq_CarrierFacts
open Aeneas Aeneas.Std Result LPi_FieldValues XRo_Join_Carriers

theorem back_claim (x : NE) : LPq_ReadPorts.backE (LPq_Powers.claim x)=x := rfl

theorem weights_from_powers (gamma : NE) (hc : canonE gamma) (g : Array NE 29#usize)
    (call : FIo_Native.weights.powers 29#usize gamma=ok g) :
    LPq_ReadPorts.WeightsCanonical (arr LPq_Powers.claim g) := by
  have canonical := LPq_OutputDomains.powers gamma hc g call
  intro v hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
  rw [back_claim]
  exact canonical x hx

theorem native_unique {H : Type} (inst : AspisR1CurrentPreparedClaim.aspis_core.Digest32 H)
    {sem : AspisR1CurrentPreparedClaim.r1_semantic.Verified H} {y1 : Slice U8}
    {g : Array AspisR1CurrentPreparedClaim.Concrete.E 29#usize}
    {inactive kappa left right : NE} (hi : canonE inactive) (hk : canonE kappa)
    (lt : LPq_PreparedTrace.Trace sem y1 g inactive kappa left)
    (rt : LPq_PreparedTrace.Trace sem y1 g inactive kappa right) : left=right := by
  have same := LPq_PreparedClaim.uniqueness inst hi hk lt rt
  have port := congrArg LPq_ReadPorts.backE same
  simpa only [back_claim] using port

#print axioms back_claim
#print axioms weights_from_powers
#print axioms native_unique
end AspisR1.LPq_CarrierFacts
