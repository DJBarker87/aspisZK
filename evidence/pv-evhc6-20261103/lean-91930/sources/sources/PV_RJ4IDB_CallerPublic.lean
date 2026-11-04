import R1Z.PV_RJDec_V047Native
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_CallerPublic
open AspisR1.PV_2TNV_PublicEncoding AspisR1.PV_2TNV_ByteEncoding
open Aeneas Aeneas.Std R1J.SpendWitnessMap AspisR1
local instance : CharP K 2147483647 :=
 charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
  AspisCircleGroupOrder.P
/-- Projection of the pinned transfer request and live transition byte record.
This is not the live plan's native record binding, which remains a separate P input. -/
def requestPublic : R0P.Public M where
 variant := .privateTransfer
 anchor := (payment (JHb_DataRequest.bytes.drop 104)).1
 nullifier := (payment (JHb_DataRequest.bytes.drop 104)).2.1
 assetId := (payment (JHb_DataRequest.bytes.drop 104)).2.2.1
 recipient := some (payment (JHb_DataRequest.bytes.drop 104)).2.2.2.1
 change := (payment (JHb_DataRequest.bytes.drop 104)).2.2.2.2
 withdrawalAmount := none
 nextPairIndex := littleEndian ((JFx_DataPublic00.bytes.drop 296).take 8)
 snapshotFrontier := fun i => digest JFx_DataPublic00.bytes (336+32*i.val)
 nextRoot := digest JFx_DataPublic00.bytes 992
 nextFrontier := fun i => digest JFx_DataPublic00.bytes (1024+32*i.val)

theorem request_public_eq : requestPublic = nativePublic := by
 unfold requestPublic nativePublic
 rw [payment_association]

def callerStatement {CH : Type} (handle : CH) :
 R0Z.ZkStatement.Statement K CH := (mapPub requestPublic,handle)

theorem caller_statement_eq {CH : Type} (handle : CH) :
 callerStatement handle = AspisR1.PV_2TNV_PublicEncoding.x handle := by
 unfold callerStatement AspisR1.PV_2TNV_PublicEncoding.x
 rw [request_public_eq]

theorem caller_fibre {CH : Type} (handle : CH) :
 ∃ w : PV_RJDec_V047.H.Instance,
 PV_RJDec_V047.H.public w = (callerStatement handle).1 :=
 PV_RJDec_V047Native.consume (callerStatement handle) handle (caller_statement_eq handle)
#print axioms request_public_eq
#print axioms caller_statement_eq
#print axioms caller_fibre
end R1Z.PV_RJ4IDB_CallerPublic
