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

/-- The semantic terminal is an independent operational parameter, even
when the complete finish pair dictionary has been selected. -/
theorem arbitrary_terminal {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (value : AspisR1PublicPreparation.aspis_core.field.QM31)
    (public : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array AspisR1PublicPreparation.aspis_core.field.QM31 29#usize) 3#usize)
    (alpha : Array AspisR1PublicPreparation.aspis_core.field.QM31 10#usize)
    (challenges : AspisR1PublicPreparation.r1_wire.Challenges) :
    let chosen := {c with boundaries:={c.boundaries with terminal:=fun _ _ _ _ => ok (.Ok value)}}
    (FIo_Install.configuration err chosen r).boundaries.terminal public claims alpha challenges=ok (.Ok value) := rfl

#print axioms retained
#print axioms claims_retained
#print axioms arbitrary_terminal
end AspisR1.FIo_SemanticSlots
end
