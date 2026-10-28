import PV_2TNV_WorldData
import PV_2TNV_HeadlineFibre
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_FinalAudit
open Aeneas Aeneas.Std PV_2TNV_PublicEncoding

/-- The same explicit mathematical witness/public pair is attached to the
source TX1 public bytes, the identical TX2 payment bytes, and the retained lane
snapshot. This is a byte/data binding; wrapper execution binding is not asserted. -/
theorem source_pair {CommitHandle : Type} (handle : CommitHandle) :
    ∃ w : PV_2TNV_HeadlineFibre.H.Instance,
      PV_2TNV_HeadlineFibre.H.public w = (x handle).1 ∧
      JHb_DataRequest.value.val.drop 104 =
        JFx_NativeBytes.publicInput.val.drop 1664 ∧
      (JHb_DataLane.value.val.drop 128).take 640 =
        (JFx_NativeBytes.publicInput.val.drop 336).take 640 := by
  exact ⟨PV_2TNV_HeadlineFibre.witness,PV_2TNV_HeadlineFibre.public_eq handle,
    PV_2TNV_SourceBytes.native_payment_bytes,PV_2TNV_WorldData.lane_snapshot_frontier⟩

#print axioms source_pair
end AspisR1.PV_2TNV_FinalAudit

#print axioms AspisR1.PV_2TNV_HeadlineFibre.fibre
#print axioms AspisR1.PV_2TNV_CanonicalWitness.fibre
#print axioms AspisR1.PV_2TNV_AppendBinding.source
#print axioms AspisR1.PV_2TNV_TransferCore.spendPlus
#print axioms AspisR1.PV_2TNV_WorldData.chunks
#print axioms AspisR1.PV_2TNV_WorldData.lane_snapshot_frontier
#print axioms AspisR1.PV_2TNV_SourceBytes.native_payment_bytes
