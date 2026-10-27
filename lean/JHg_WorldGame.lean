import JHg_AuditWorld
import JFv_WorldAdmission
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_WorldGame
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open JHg_World CPG_Projection CPP_BankState Hist_RuntimeEntry
attribute [local irreducible] JHb_Header.account JFx_NativeBytes.checkpoint JFx_NativeBytes.publicInput

theorem game (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second) :
    CPH_Game.DeployedPairExecution observations false true e1 e2 JFv_World.saved [] n1 n2
      CPH_FixtureData.copy CPH_FixtureData.allocator CPH_Program.verifier := by
  refine ⟨⟨⟨rfl,rfl⟩,rfl,rfl⟩,⟨rfl,rfl,List.not_mem_nil⟩,rfl,⟨⟨rfl,rfl,?_⟩,?_⟩⟩
  · exact CPG_RuntimeTrace.Executes.nil _
  · exact CPG_RuntimeTrace.Executes.nil _
#print axioms game

theorem persistence (system : S2W_ExtractionBoundary.Program) :
    CPR_DataPersistence.TwoTransactionLaw
      (adjacent observations) (ordinary observations system) (before observations)
      (tentative observations) (success observations) (loaded observations) := by
  intro t u linked key eligible
  have ht : t=false := linked.1.1
  have hu : u=true := linked.1.2
  subst t;subst u
  rfl
#print axioms persistence

theorem first : S2W_D189Consolidation.RuntimeEntrypointAdmission
    (model (Nat → Record)) e1 e1.heap 3 := by
  apply CPH_FixtureEntry.admitted
  · intro a
    change a ≠ a+100
    omega
  · intro a small
    change a<8
    omega
  · intro c
    rfl
#print axioms first

theorem second : S2W_D189Consolidation.RuntimeEntrypointAdmission
    (model (Nat → Record)) e2 e2.heap 7 := by
  apply CPH_FixtureEntry.admitted
  · intro a
    change CPH_FixtureData.readerCell a ≠ CPH_FixtureData.readerCell a+100
    omega
  · intro a small
    exact CPH_FixtureAdmission.reader_bound a small
  · intro c
    rfl
#print axioms second
end AspisR1.JHg_WorldGame
end
