import R1Z.PDict_RemainingDictionary231
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingExt231
open Aeneas Aeneas.Std Result ProverRwFull
@[reducible] def replace [ExternalTypes] (ops other : ExternalFuns) : ExternalFuns :=
  {ops with op78 := @other.op78, op231 := other.op231, op247 := other.op247}

theorem stage0 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwOuterTag.selected types (@replace types ops other) =
    @replace types (@ProverRwOuterTag.selected types ops) other := rfl
#print axioms replace
#print axioms stage0
end R1Z.PDict_RemainingExt231
