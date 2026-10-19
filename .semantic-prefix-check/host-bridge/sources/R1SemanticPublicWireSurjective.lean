import R1SemanticPublicWire

/-! Canonical public-model records have a typed wire-carrier representative.
This constructs a model value only; it does not assert any source parser or
serializer correspondence. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicWireSurjective

open AspisR1.SemanticPublicWire

theorem exists_wire (pub : R0P.Public M31)
    (hc : PublicOptionShape.canonical pub)
    (hi : pub.nextPairIndex < 2^64) :
    ∃ wire : Wire, toPublic wire = pub := by
  cases pub with
  | mk variant anchor nullifier assetId recipient change withdrawalAmount
      nextPairIndex snapshotFrontier nextRoot nextFrontier =>
    cases hv : variant with
    | privateTransfer =>
        obtain ⟨recipientValue, hrecipient, hwithdrawal⟩ :=
          PublicOptionShape.private_transfer_shape _ hv hc
        change recipient = some recipientValue at hrecipient
        change withdrawalAmount = none at hwithdrawal
        subst recipient
        subst withdrawalAmount
        let common : Common := {
          anchor := anchor
          nullifier := nullifier
          assetId := assetId
          change := change
          nextPairIndex := ⟨nextPairIndex, hi⟩
          snapshotFrontier := snapshotFrontier
          nextRoot := nextRoot
          nextFrontier := nextFrontier
        }
        exact ⟨.transfer common recipientValue, by simp [toPublic, common, hv]⟩
    | withdrawal =>
        obtain ⟨amount, hnonzero, hwithdrawal, hrecipient⟩ :=
          PublicOptionShape.withdrawal_shape _ hv hc
        change withdrawalAmount = some amount at hwithdrawal
        change recipient = none at hrecipient
        subst recipient
        subst withdrawalAmount
        let common : Common := {
          anchor := anchor
          nullifier := nullifier
          assetId := assetId
          change := change
          nextPairIndex := ⟨nextPairIndex, hi⟩
          snapshotFrontier := snapshotFrontier
          nextRoot := nextRoot
          nextFrontier := nextFrontier
        }
        exact ⟨.withdrawal common amount, by simp [toPublic, common, hv]⟩

#print axioms exists_wire
end AspisR1.SemanticPublicWireSurjective
