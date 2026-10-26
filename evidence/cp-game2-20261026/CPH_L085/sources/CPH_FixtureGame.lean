import CPH_FixtureData
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_FixtureGame
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry CPH_FixtureData

theorem game : CPH_Game.DeployedPairExecution observations false true e1 e2 saved suffix n1 n2 copy allocator id := by
  refine ⟨⟨⟨rfl,rfl⟩,rfl,rfl⟩,⟨rfl,rfl,List.not_mem_nil⟩,rfl,⟨⟨rfl,rfl,?_⟩,?_⟩⟩
  · exact CPG_RuntimeTrace.executes n1 n2 copy allocator id
      (CPR_SourceBank.afterCopy (cached initial) 2 saved) suffix
  · exact CPG_RuntimeTrace.Executes.nil (cached final)

theorem persistence (system : S2W_ExtractionBoundary.Program) :
    CPR_DataPersistence.TwoTransactionLaw
      (adjacent observations) (ordinary observations system) (before observations)
      (tentative observations) (success observations) (loaded observations) := by
  intro t u linked key eligible
  have ht : t = false := linked.1.1
  have hu : u = true := linked.1.2
  subst t
  subst u
  rfl

#print axioms game
#print axioms persistence
end AspisR1.CPH_FixtureGame
end
