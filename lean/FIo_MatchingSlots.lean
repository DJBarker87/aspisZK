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
    (Tx1Q_QueryBridge.leaves (FIo_Install.configuration err c r).query).op20=c.query.op20 ∧
    (Tx1Q_QueryBridge.leaves (FIo_Install.configuration err c r).query).widePartialEq=c.query.widePartialEq := ⟨rfl,rfl,rfl⟩

/-- The exact same remaining configuration can select ANY successful
first-fold result. Installing FinishOps adds no constraint on this source call. -/
theorem arbitrary_fold {C : Type} (err : C) (c : Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (value alpha : AspisR1Stage2.Stage2Finish.E)
    (dots : Array AspisR1Stage2.Stage2Finish.E 4#usize) (inverse : Array U32 5#usize) :
    let chosen := {c with query:={c.query with op17:=fun _ _ _ => ok value}}
    (FIo_Install.configuration err chosen r).query.op17 alpha dots inverse=ok value := rfl

#print axioms retained
#print axioms q1_retained
#print axioms arbitrary_fold
end AspisR1.FIo_MatchingSlots
end
