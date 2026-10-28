import NBA_Carriers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBA_PowersCallee
open Aeneas Aeneas.Std Result AspisR1ClaimPreparedBridge LPi_FieldValues

theorem source (N : Usize) (x : NE) (hx : canonE x) :
    ∃ out, FIo_Native.weights.powers N x=ok out ∧
      NBA_Installed.actual.powers N (NBA_ClaimCallee.wide x)=
        ok (mapArray NBA_ClaimCallee.wide out) ∧
      (∀ z ∈ out.val, canonE z) := by
  obtain ⟨out,native,cohort⟩ := LPq_Powers.source N x hx
  refine ⟨out,native,?_,LPq_OutputDomains.powers x hx out native⟩
  rw [NBA_Installed.powers_slot]
  unfold powersPublic
  rw [NBA_ClaimCallee.port,cohort,bind_tc_ok]
  rfl

#print axioms source
end AspisR1.NBA_PowersCallee
end
