import F3N_PreparedCells
set_option autoImplicit false
namespace AspisR1.F3P_CircleInstall
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem installed (B : FinishModel.Boundaries) (block : Array U8 32#usize)
    (row : FinishModel.CircleRow) :
    (F3M_CircleSource.install B).circle block row=F3M_CircleSource.source block row := rfl

theorem finish_install (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (block : Array U8 32#usize) (row : FinishModel.CircleRow) :
    (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std (F3M_CircleSource.install B))).circle block row=
      F3M_CircleSource.source block row := rfl

#print axioms installed
#print axioms finish_install
end AspisR1.F3P_CircleInstall
