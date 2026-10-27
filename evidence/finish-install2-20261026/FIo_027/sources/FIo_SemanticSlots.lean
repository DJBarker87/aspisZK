import FIo_Accepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_SemanticSlots
open Aeneas Aeneas.Std Result
open DrvC_Installation

theorem retained {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (FIo_Install.configuration err c r).boundaries.mask=c.boundaries.mask ∧
    (FIo_Install.configuration err c r).boundaries.add=c.boundaries.add ∧
    (FIo_Install.configuration err c r).boundaries.mul=c.boundaries.mul ∧
    (FIo_Install.configuration err c r).boundaries.terminal=c.boundaries.terminal := ⟨rfl,rfl,rfl,rfl⟩

theorem claims_retained (std : ClaimsUnrolledFinish.StdCalls)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    (ClaimsUnrolledFinish.install std B).terminal=B.terminal ∧
    (ClaimsUnrolledFinish.install std B).mask=B.mask ∧
    (ClaimsUnrolledFinish.install std B).add=B.add ∧
    (ClaimsUnrolledFinish.install std B).mul=B.mul := ⟨rfl,rfl,rfl,rfl⟩

#print axioms retained
#print axioms claims_retained
end AspisR1.FIo_SemanticSlots
end
