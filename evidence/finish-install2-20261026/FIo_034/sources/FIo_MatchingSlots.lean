import FIo_Accepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_MatchingSlots
open Aeneas Aeneas.Std Result
open DrvC_Installation

theorem retained {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (FIo_Install.configuration err c r).query.op17=c.query.op17 ∧
    (FIo_Install.configuration err c r).query.op20=c.query.op20 ∧
    (FIo_Install.configuration err c r).query.widePartialEq=c.query.widePartialEq := ⟨rfl,rfl,rfl⟩

theorem q1_retained {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (Tx1Q_QueryBridge.leaves (FIo_Install.configuration err c r).query).op17=c.query.op17 ∧
    (Tx1Q_QueryBridge.leaves (FIo_Install.configuration err c r).query).op20=c.query.op20 := ⟨rfl,rfl⟩

#print axioms retained
#print axioms q1_retained
end AspisR1.FIo_MatchingSlots
end
