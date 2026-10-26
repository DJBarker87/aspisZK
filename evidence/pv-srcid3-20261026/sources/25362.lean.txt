import R1Z.PV_Src_CheckedCanonical

/-! Canonical source snapshot encoding: frontier canonicality is proved from
field encoding, while native snapshot selection remains an explicit join. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CanonicalSnapshot
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
open BuilderForestAdmissionPort.pool_v1

def native (pub : R0P.Public F) (bound : pub.nextPairIndex < 2^64)
    (pool domain : PV_Src_PublicRecords.Context) : pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  pool := pool
  deployment_domain := domain
  sequence := UScalar.ofNatCore pub.nextPairIndex bound
  next_pair_index := UScalar.ofNatCore pub.nextPairIndex bound
  current_root := d32 pub.anchor
  frontier := arr20 (fun l => d32 (pub.snapshotFrontier l))

theorem frontier_canonical (pub : R0P.Public F) (bound : pub.nextPairIndex < 2^64)
    (pool domain : PV_Src_PublicRecords.Context) (l : Fin 20) :
    Canon8 (native pub bound pool domain).frontier.val[l.val]! := by
  rw [native,arr20_get _ _ l.isLt]
  exact d32_canon _

theorem next_index (pub : R0P.Public F) (bound : pub.nextPairIndex < 2^64)
    (pool domain : PV_Src_PublicRecords.Context) :
    (native pub bound pool domain).next_pair_index.val = pub.nextPairIndex :=
  UScalar.ofNatCore_val_eq _

theorem sequence (pub : R0P.Public F) (bound : pub.nextPairIndex < 2^64)
    (pool domain : PV_Src_PublicRecords.Context) :
    (native pub bound pool domain).sequence = (native pub bound pool domain).next_pair_index := rfl

#print axioms frontier_canonical
#print axioms next_index
#print axioms sequence
end R1Z.PV_Src_CanonicalSnapshot
