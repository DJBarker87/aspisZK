import FIo_FieldBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_ConcreteDictionary
open AspisR1Stage2.Stage2Finish

theorem seed_independent (r : NP6_StdModel.Reservation) (a b : FinishOps FIo_Install.W) :
    FIo_Install.finishOps r a=FIo_Install.finishOps r b := rfl

theorem fixed {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (FIo_Install.configuration err c r).finish=FIo_Install.finishOps r c.finish := rfl

theorem decoded (x : FIo_FieldBridge.NE) :
    CheckpointBytes5Output.ofE (FIo_Install.fromE x)=
      AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide x) := rfl

#print axioms seed_independent
#print axioms fixed
#print axioms decoded
end AspisR1.FIo_ConcreteDictionary
end
