import CPH_FixtureGame
import CPH_FixtureAdmission
import CPH_FixtureWrappers
import ARR_OracleLoss
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_GameLoss
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry CPH_FixtureData

/-- Diagnostic native reader that attempts the actual digest helper and fails.
No extraction instance for the deployed installation is asserted. -/
def rejecting (parts : SdkC_Source.Parts) : S2W_ExtractionBoundary.Second :=
  fun _ _ _ _ => do
    let _ ← S2W_DigestExtraction.digest SCG_PartialOracle.failingOracle () parts
    ok (.Ok ())

theorem rejects (parts : SdkC_Source.Parts) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    second (rejecting parts) allocator e2 id data slot () = .fail .assertionFailure := by
  simp only [second,CPH_FixtureReserve.reserve_ok,rejecting,
    S2W_DigestExtraction.digest_eq_hashv,SCG_PartialOracle.failingOracle,bind_tc_fail,bind_tc_ok]

/-- The approved four game fields and persistence do not impose TX2 success
or a total syscall. This is an actual instance of those fields, but deliberately
not an instance of the installed source/extraction/finish conjunction. -/
theorem allowed (parts : SdkC_Source.Parts) :
    CPH_Game.DeployedPairExecution observations false true e1 e2 saved suffix n1 (rejecting parts) copy allocator id := by
  refine ⟨CPH_FixtureGame.game.consecutive,CPH_FixtureGame.game.checkpoint,
    CPH_FixtureGame.game.parent,⟨⟨rfl,rfl,?_⟩,?_⟩⟩
  · have trace := CPG_RuntimeTrace.executes n1 (rejecting parts) copy allocator id
      (CPR_SourceBank.afterCopy (cached initial) 2 saved) suffix
    have same : CPP_BankHistory.run n1 (rejecting parts) copy allocator id
        (CPR_SourceBank.afterCopy (cached initial) 2 saved) suffix =
      CPP_BankHistory.run n1 n2 copy allocator id
        (CPR_SourceBank.afterCopy (cached initial) 2 saved) suffix := by
      rfl
    rw [same] at trace
    exact trace
  · exact CPG_RuntimeTrace.Executes.nil (cached final)

#print axioms rejects
#print axioms allowed
#print axioms CPH_FixtureAdmission.admitted1
#print axioms CPH_FixtureAdmission.admitted2
#print axioms CPH_FixtureGame.persistence
#print axioms CPH_FixtureWrappers.first_success
end AspisR1.ARS_GameLoss
end
