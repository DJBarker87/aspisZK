import NLJ_PrepareGoal
import NLJ_Monad
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareSource
open Aeneas Aeneas.Std Result AspisR1CurrentCaller AspisR1PublicPreparation
/-- Exact source equality only; no native or child-domain admission follows. -/
theorem source (cfg : NLJ_Prepare.Configuration) {H : Type}
 (i : NLJ_Prepare.Input H) : NLJ_Prepare.SourceEquality cfg i := by
 rfl
#print axioms source
end AspisR1.NLR_PrepareSource
end
