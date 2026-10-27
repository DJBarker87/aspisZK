import RPz8_CPH_BankSuffix
import RPz8_SCE_FixtureData
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_FixtureBank
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPP_BankState Hist_RuntimeEntry Hist_Store SCE_FixtureData

theorem result :
    CPP_BankHistory.run n1 n2 copy allocator id
      (CPR_SourceBank.afterCopy (cached initial) 2 saved) suffix =
      (⟨(CPR_SourceBank.afterCopy (cached initial) 2 saved).cells,
        S2Trust.put (cached initial).lamports 2 6⟩,[.rollback,.rollback,.rollback]) :=
  CPH_BankSuffix.credit_live n1 n2 copy allocator id
    (CPR_SourceBank.afterCopy (cached initial) 2 saved) 2 5 (by decide)

theorem final_cells : final.cells = (CPR_SourceBank.afterCopy (cached initial) 2 saved).cells :=
  congrArg (fun p => p.1.cells) result

theorem final_balance : final.lamports 2 = 6 := by
  have same := congrArg (fun p => p.1.lamports 2) result
  exact same

theorem final_data : (final.cells 2).data = saved.deref := by
  rw [final_cells]
  exact congrArg (fun cell => cell.data) (Hist_Store.put_here _ _ _)

#print axioms result
#print axioms final_cells
#print axioms final_balance
#print axioms final_data
end AspisR1.SCE_FixtureBank
end
