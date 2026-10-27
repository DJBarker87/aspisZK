import Tx2N_Powers
import RPz7_Tx2I_Install
import Port4A_ReaderInstall
import Port5Q1_QueryPorts
import Port4C_RowStd
import Port3_QueryStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Install
open Aeneas Aeneas.Std Result VTop_Stages

def inner (base : Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops) : Ops :=
  {base with
    op18 := Port4A_ReaderInstall.reader reserved
    op6 := Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install query))
    op9 := Port3_FlushInstall.flush
    op17 := Tx2N_Powers.powers}

theorem slots (base : Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops) :
    @(inner base reserved query).op18 = @Port4A_ReaderInstall.reader reserved ∧
    (inner base reserved query).op6 =
      Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install query)) ∧
    (inner base reserved query).op9 = Port3_FlushInstall.flush ∧
    (inner base reserved query).op17 = Tx2N_Powers.powers := ⟨rfl,rfl,rfl,rfl⟩

theorem retained (base : Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops) :
    {inner base reserved query with op18 := base.op18, op6 := base.op6, op9 := base.op9, op17 := base.op17} = base := by
  cases base; rfl

theorem reader_success (base : Ops) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (checkpoint proof pub : Slice U8) (variant : transport.Variant)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : (inner base reserved query).op18 D checkpoint proof pub variant hash = ok (.Ok (p,a))) :
    AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      (VTop_Checkpoint.digest D) checkpoint proof pub variant hash = ok (.Ok (p,a)) :=
  Port4A_ReaderInstall.accepted_source base reserved D hash checkpoint proof pub variant p a success

#print axioms slots
#print axioms retained
#print axioms reader_success
end AspisR1.Tx2N_Install
end
