import R1SemanticPublicWire

/-! Canonical public-model records have a typed wire-carrier representative.
This constructs a model value only; it does not assert any source parser or
serializer correspondence.
PIN2 (2026-11-10): the representative carries the 32-byte pool, deployment
domain and (withdrawal only) destination fields. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicWireSurjective

open AspisR1.SemanticPublicWire

theorem exists_wire (pub : R0P.Public M31)
    (hc : PublicOptionShape.canonical pub)
    (hi : pub.nextPairIndex < 2^64) :
    ∃ wire : Wire, toPublic wire = pub := by
  obtain ⟨hpool, hdomain, _⟩ := PublicOptionShape.canonical_bindingLengths pub hc
  cases pub with
  | mk variant anchor nullifier assetId recipient change withdrawalAmount
      nextPairIndex snapshotFrontier nextRoot nextFrontier pool deploymentDomain destination =>
    cases hv : variant with
    | privateTransfer =>
        obtain ⟨recipientValue, hrecipient, hwithdrawal⟩ :=
          PublicOptionShape.private_transfer_shape _ hv hc
        have hdest := PublicOptionShape.private_transfer_destination _ hv hc
        change recipient = some recipientValue at hrecipient
        change withdrawalAmount = none at hwithdrawal
        change destination = none at hdest
        subst recipient
        subst withdrawalAmount
        subst destination
        let common : Common := {
          anchor := anchor
          nullifier := nullifier
          assetId := assetId
          change := change
          nextPairIndex := ⟨nextPairIndex, hi⟩
          snapshotFrontier := snapshotFrontier
          nextRoot := nextRoot
          nextFrontier := nextFrontier
          pool := ⟨pool, hpool⟩
          deploymentDomain := ⟨deploymentDomain, hdomain⟩
          destination := none
        }
        exact ⟨.transfer common recipientValue, by simp [toPublic, common, hv]⟩
    | withdrawal =>
        obtain ⟨amount, hnonzero, hwithdrawal, hrecipient⟩ :=
          PublicOptionShape.withdrawal_shape _ hv hc
        obtain ⟨d, hdest, hdlen⟩ := PublicOptionShape.withdrawal_destination _ hv hc
        change withdrawalAmount = some amount at hwithdrawal
        change recipient = none at hrecipient
        change destination = some d at hdest
        subst recipient
        subst withdrawalAmount
        subst destination
        let common : Common := {
          anchor := anchor
          nullifier := nullifier
          assetId := assetId
          change := change
          nextPairIndex := ⟨nextPairIndex, hi⟩
          snapshotFrontier := snapshotFrontier
          nextRoot := nextRoot
          nextFrontier := nextFrontier
          pool := ⟨pool, hpool⟩
          deploymentDomain := ⟨deploymentDomain, hdomain⟩
          destination := some ⟨d, hdlen⟩
        }
        exact ⟨.withdrawal common amount, by simp [toPublic, common, hv]⟩

#print axioms exists_wire
end AspisR1.SemanticPublicWireSurjective
