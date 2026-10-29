import PV_RJ4IDB_CallerLive
/-! Source-level typed projection of semantic_public/private_public. Context
keys/sequences/current root remain in the full statement byte observation;
Rust's semantic public projection itself selects the fields below. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_CallerSemantic
open AspisR1 PV_2TNV_PublicEncoding PV_2TNV_ByteEncoding
open Aeneas Aeneas.Std R1J.SpendWitnessMap
local instance : CharP K 2147483647 :=
 charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
  AspisCircleGroupOrder.P
structure Transfer where
 anchor : R0P.Digest M
 nullifier : R0P.Digest M
 assetId : M
 recipient : R0P.Digest M
 change : R0P.Digest M
structure Transition where
 nextPairIndex : Nat
 snapshotFrontier : Fin 20 → R0P.Digest M
 nextRoot : R0P.Digest M
 nextFrontier : Fin 20 → R0P.Digest M

def semanticPublic (p : Transfer) (t : Transition) : R0P.Public M where
 variant := .privateTransfer
 anchor := p.anchor
 nullifier := p.nullifier
 assetId := p.assetId
 recipient := some p.recipient
 change := p.change
 withdrawalAmount := none
 nextPairIndex := t.nextPairIndex
 snapshotFrontier := t.snapshotFrontier
 nextRoot := t.nextRoot
 nextFrontier := t.nextFrontier

def requestTransfer : Transfer :=
 ⟨(payment (JHb_DataRequest.bytes.drop 104)).1,
 (payment (JHb_DataRequest.bytes.drop 104)).2.1,
 (payment (JHb_DataRequest.bytes.drop 104)).2.2.1,
 (payment (JHb_DataRequest.bytes.drop 104)).2.2.2.1,
 (payment (JHb_DataRequest.bytes.drop 104)).2.2.2.2⟩

def liveTransition : Transition :=
 ⟨littleEndian ((JHb_DataLane.value.val.drop 88).take 8),
 fun i => digest JHb_DataLane.value.val (128+32*i.val),
 digest JFx_DataPublic00.bytes 992,
 fun i => digest JFx_DataPublic00.bytes (1024+32*i.val)⟩

theorem typed_projection : semanticPublic requestTransfer liveTransition =
 PV_RJ4IDB_CallerLive.livePublic := rfl

def caller {CH : Type} (native_handle : CH) : R0Z.ZkStatement.Statement K CH :=
 (mapPub (semanticPublic requestTransfer liveTransition),native_handle)

theorem caller_to_transfer13 {CH : Type} (native_handle : CH) :
 caller native_handle = PV_2TNV_PublicEncoding.x native_handle := by
 unfold caller
 rw [typed_projection]
 exact PV_RJ4IDB_CallerLive.caller_to_transfer13 native_handle

theorem consume {CH : Type} (native_handle : CH) :
 ∃ w : PV_RJDec_V047.H.Instance, PV_RJDec_V047.H.public w = (caller native_handle).1 :=
 PV_RJDec_V047Native.consume (caller native_handle) native_handle (caller_to_transfer13 native_handle)
#print axioms typed_projection
#print axioms caller_to_transfer13
#print axioms consume
end R1Z.PV_RJ4IDB_CallerSemantic
