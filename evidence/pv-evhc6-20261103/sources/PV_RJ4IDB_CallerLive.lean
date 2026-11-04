import PV_RJ4IDB_ByteWindow
import PV_RJ4IDB_CallerPublic
import PV_2TNV_WorldData
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_CallerLive
open AspisR1 Aeneas Aeneas.Std
open PV_2TNV_PublicEncoding PV_2TNV_ByteEncoding
open R1J.SpendWitnessMap
local instance : CharP K 2147483647 :=
 charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
  AspisCircleGroupOrder.P

theorem live_index : littleEndian ((JHb_DataLane.value.val.drop 88).take 8) =
 nativePublic.nextPairIndex :=
 congrArg littleEndian PV_2TNV_WorldData.lane_snapshot_index

theorem live_frontier (i : Fin 20) :
 digest JHb_DataLane.value.val (128+32*i.val) =
 digest JFx_DataPublic00.bytes (336+32*i.val) :=
 PV_RJ4IDB_ByteWindow.digest_window _ _ 128 336 640 (32*i.val)
 PV_2TNV_WorldData.lane_snapshot_frontier (by have hi := i.isLt; omega)

/-- The source caller's payment comes from the request, while its live index
and frontier come from the lane record. The candidate afterstate remains the
pinned transfer-13 output record. Native decoder/compiler binding is separate. -/
def livePublic : R0P.Public M :=
 {PV_RJ4IDB_CallerPublic.requestPublic with
 nextPairIndex := littleEndian ((JHb_DataLane.value.val.drop 88).take 8)
 snapshotFrontier := fun i => digest JHb_DataLane.value.val (128+32*i.val)}

theorem live_public_eq : livePublic = nativePublic := by
 have hf : (fun i : Fin 20 => digest JHb_DataLane.value.val (128+32*i.val)) =
   (fun i : Fin 20 => digest JFx_DataPublic00.bytes (336+32*i.val)) := by
  funext i
  exact live_frontier i
 unfold livePublic
 rw [live_index,hf,PV_RJ4IDB_CallerPublic.request_public_eq]
 rfl

def callerStatement {CH : Type} (handle : CH) : R0Z.ZkStatement.Statement K CH :=
 (mapPub livePublic,handle)

theorem caller_to_transfer13 {CH : Type} (native_handle : CH) :
 callerStatement native_handle = PV_2TNV_PublicEncoding.x native_handle := by
 unfold callerStatement PV_2TNV_PublicEncoding.x
 rw [live_public_eq]

theorem caller_witness {CH : Type} (native_handle : CH) :
 ∃ w : PV_RJDec_V047.H.Instance,
 PV_RJDec_V047.H.public w = (callerStatement native_handle).1 :=
 PV_RJDec_V047Native.consume (callerStatement native_handle) native_handle
 (caller_to_transfer13 native_handle)
#print axioms live_index
#print axioms live_frontier
#print axioms live_public_eq
#print axioms caller_to_transfer13
#print axioms caller_witness
end R1Z.PV_RJ4IDB_CallerLive
