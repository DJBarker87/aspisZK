import PV_2TNV_ByteEncoding
import R1Z.PV_RunJoin_CanonicalFixtures
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_PublicEncoding
open Aeneas Aeneas.Std
open R1Z R1J.SpendWitnessMap
open PV_2TNV_ByteEncoding
abbrev M := R1Z.PV_RunJoin_FixtureRecords.M
abbrev K := R1Z.PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

/-- Read one little-endian field word at its source byte offset. -/
def word (bytes : List U8) (off : Nat) : M :=
  littleEndian ((bytes.drop off).take 4)
def digest (bytes : List U8) (off : Nat) : R0P.Digest M :=
  fun i => word bytes (off + 4*i.val)

/-- The payment projection deliberately has no snapshot/afterstate fields. -/
def payment (bytes : List U8) : R0P.Digest M × R0P.Digest M × M ×
    R0P.Digest M × R0P.Digest M :=
  (digest bytes 80, digest bytes 112, word bytes 144,
    digest bytes 152, digest bytes 184)

/-- Equality of complete native payment suffixes, before any field mapping. -/
theorem payment_association :
    payment (JHb_DataRequest.bytes.drop 104) =
      payment (JFx_DataPublic00.bytes.drop 1664) :=
  congrArg payment payment_same

/-- Transfer-13's headline public projection. Context keys and sequences remain
in the enclosing native byte record; the spend public retains index/frontiers. -/
def nativePublic : R0P.Public M where
  variant := .privateTransfer
  anchor := (payment (JFx_DataPublic00.bytes.drop 1664)).1
  nullifier := (payment (JFx_DataPublic00.bytes.drop 1664)).2.1
  assetId := (payment (JFx_DataPublic00.bytes.drop 1664)).2.2.1
  recipient := some (payment (JFx_DataPublic00.bytes.drop 1664)).2.2.2.1
  change := (payment (JFx_DataPublic00.bytes.drop 1664)).2.2.2.2
  withdrawalAmount := none
  nextPairIndex := littleEndian ((JFx_DataPublic00.bytes.drop 296).take 8)
  snapshotFrontier := fun i => digest JFx_DataPublic00.bytes (336 + 32*i.val)
  nextRoot := digest JFx_DataPublic00.bytes 992
  nextFrontier := fun i => digest JFx_DataPublic00.bytes (1024 + 32*i.val)

def x {CommitHandle : Type} (handle : CommitHandle) :
    R0Z.ZkStatement.Statement K CommitHandle := (mapPub nativePublic,handle)

theorem native_index : nativePublic.nextPairIndex = 13 := snapshot_index_value

theorem statement_index {CommitHandle : Type} (handle : CommitHandle) :
    (x handle).1.nextPairIndex = 13 := native_index

/-- The original runjoin index-zero witness is not a matching witness for the
joint fixture statement. This does not assert that the new fibre is empty. -/
theorem original_transfer_not_matching {CommitHandle : Type} (handle : CommitHandle) :
    (BuilderSource.prover (K := K)).public PV_RunJoin_CanonicalFixtures.transfer ≠
      (x handle).1 := by
  intro same
  have indices := congrArg (fun p : R0P.Public K => p.nextPairIndex) same
  change 0 = nativePublic.nextPairIndex at indices
  rw [native_index] at indices
  omega

#print axioms payment_association
#print axioms native_index
#print axioms statement_index
#print axioms original_transfer_not_matching
end AspisR1.PV_2TNV_PublicEncoding
