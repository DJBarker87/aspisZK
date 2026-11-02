import PV_BR_R1Z_PV_RJDec_V047
import PV_BR_FixtureBundle
import PV_BR_PV_RJ4IDB_ByteWindow

/- Original source module R1Z.PV_RJDec_V047Native; sha256 a64651ed9c74fe343f35db71da5089540de76457ac4694f6720c2194166f824b. -/
section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_V047Native
open R0Z.ZkStatement
local notation "K" => PrivacyR1AcctBasis.K
/-- The original transfer-13 fibre is supplied here, rather than left as a
premise. The actual native statement equality is still an explicit obligation.
No wrapper execution or FixturePdaRuntime law is consumed by this theorem. -/
theorem consume {CH : Type} (actual : Statement K CH) (native_handle : CH)
    (native_identification : actual = AspisR1.PV_2TNV_PublicEncoding.x native_handle) :
    ∃ w : PV_RJDec_V047.H.Instance, PV_RJDec_V047.H.public w = actual.1 :=
  PV_RJDec_V047.consume (AspisR1.PV_2TNV_PublicEncoding.x native_handle) actual
    (AspisR1.PV_2TNV_HeadlineFibre.fibre native_handle) native_identification

/-- Full statement identity has two components. This criterion does not erase
or alter the native commitment handle to obtain public-component equality. -/
theorem identification_iff {CH : Type} (actual : Statement K CH) (native_handle : CH) :
    actual = AspisR1.PV_2TNV_PublicEncoding.x native_handle ↔
    actual.1 = (AspisR1.PV_2TNV_PublicEncoding.x native_handle).1 ∧
    actual.2 = native_handle := by
  constructor
  · intro eq
    exact ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  · rintro ⟨public_eq,handle_eq⟩
    exact Prod.ext public_eq handle_eq
#print axioms consume
#print axioms identification_iff
end R1Z.PV_RJDec_V047Native

end
end

/- Original source module PV_RJ4IDB_CallerPublic; sha256 626670195d2412553d214d9b9bf2479df9cd498c60cf5165f22b08dc2f50f12f. -/
section
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

end
end

/- Original source module PV_RJ4IDB_CallerLive; sha256 e7f150b4417c2033d5b28b7cf148e174daba855609eb8cf6bc87a399584d9d24. -/
section
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

end
end
