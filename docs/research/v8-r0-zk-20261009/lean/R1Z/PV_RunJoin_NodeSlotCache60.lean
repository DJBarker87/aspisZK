import R1Z.PV_RunJoin_ActualPublication60
import R1Z.PV_RunJoin_NodePayloadModel60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NodeSlotCache60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
variable [ExternalTypes] [ExternalFuns]

def batch (i : Fin 6) : Usize := UScalar.ofNatCore (i.val/3)
  (by have hs := ProverCommitPairCounter47.usize_large;rw [UScalar.size_def] at hs;have := i.isLt;omega)
def tree (i : Fin 6) : Usize := UScalar.ofNatCore (i.val%3)
  (by have hs := ProverCommitPairCounter47.usize_large;rw [UScalar.size_def] at hs;have := i.isLt;omega)
def capacity (i : Fin 6) : Nat := 32*([146,146,128,172,172,150][i.val]?.getD 0)

theorem actual (phase : Phase) (p : prover.Publication) (i : Fin 6)
    (context : PV_RunJoin_PublishContext57.QueryContext (PV_RunJoin_ActualRun.runs phase) p) :
    PV_RunJoin_ActualPlanSources59.slot phase i=
      PV_RunJoin_NodePayloadModel60.model (PV_RunJoin_ActualPlanSources59.nodeBytes p (batch i) (tree i)) (capacity i) := by
  simp only [PV_RunJoin_ActualPlanSources59.slot,PV_RunJoin_ActualPublication60.returned phase p context]
  rfl

#print axioms actual
end R1Z.PV_RunJoin_NodeSlotCache60
