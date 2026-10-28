import R1Z.PV_RunJoin_PublicCore21
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicExt21
local notation "M" => PV_RunJoin_FixtureRecords.M
/-- Fieldwise equality, without reducing any concrete hash or append recurrence. -/
theorem source (a b : R0P.Public M)
    (hv : a.variant = b.variant) (ha : a.anchor = b.anchor)
    (hn : a.nullifier = b.nullifier) (hi : a.assetId = b.assetId)
    (hr : a.recipient = b.recipient) (hc : a.change = b.change)
    (hw : a.withdrawalAmount = b.withdrawalAmount) (hp : a.nextPairIndex = b.nextPairIndex)
    (hs : a.snapshotFrontier = b.snapshotFrontier) (ht : a.nextRoot = b.nextRoot)
    (hf : a.nextFrontier = b.nextFrontier) : a = b := by
  cases a
  cases b
  congr 1 <;> assumption
#print axioms source
end R1Z.PV_RunJoin_PublicExt21
