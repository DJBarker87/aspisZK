import R0P.Core

/-! A small executable predicate for the option/variant shape represented by
`R0P.Public`. This does not parse Rust bytes and does not impose value bounds.

PIN2 (2026-11-10): the shape also fixes the binding suffix appended to
`public_bytes`: `pool` and `deploymentDomain` have 32 bytes, and the
destination token account (32 bytes) is present exactly for a withdrawal. -/
set_option autoImplicit false

namespace AspisR1.PublicOptionShape

open R0P

variable {K : Type} [Field K] [DecidableEq K]

/-- Lengths of the PIN2 binding fields. -/
def bindingLengths (pub : Public K) : Prop :=
  pub.pool.length = 32 ∧ pub.deploymentDomain.length = 32 ∧
    ∀ d, pub.destination = some d → d.length = 32

def bindingLengthsCheck (pub : Public K) : Bool :=
  pub.pool.length == 32 && pub.deploymentDomain.length == 32 &&
    (match pub.destination with
     | none => true
     | some d => d.length == 32)

def canonical (pub : Public K) : Prop :=
  match pub.variant with
  | .privateTransfer => pub.recipient.isSome = true ∧ pub.withdrawalAmount = none ∧
      pub.destination = none ∧ bindingLengths pub
  | .withdrawal => pub.recipient.isNone = true ∧ pub.withdrawalAmount.isSome = true ∧
      pub.withdrawalAmount ≠ some 0 ∧ pub.destination.isSome = true ∧ bindingLengths pub

def check (pub : Public K) : Bool :=
  match pub.variant with
  | .privateTransfer => pub.recipient.isSome && pub.withdrawalAmount.isNone &&
      pub.destination.isNone && bindingLengthsCheck pub
  | .withdrawal => pub.recipient.isNone && pub.withdrawalAmount.isSome &&
      pub.withdrawalAmount != some 0 && pub.destination.isSome && bindingLengthsCheck pub

theorem bindingLengthsCheck_eq_true_iff (pub : Public K) :
    bindingLengthsCheck pub = true ↔ bindingLengths pub := by
  cases hd : pub.destination <;> simp [bindingLengthsCheck, bindingLengths, hd, and_assoc]

theorem check_eq_true_iff (pub : Public K) : check pub = true ↔ canonical pub := by
  cases hv : pub.variant <;>
    simp [check, canonical, hv, and_assoc, bindingLengthsCheck_eq_true_iff]

theorem private_transfer_shape (pub : Public K)
    (hvariant : pub.variant = .privateTransfer) (hcanonical : canonical pub) :
    ∃ recipient, pub.recipient = some recipient ∧ pub.withdrawalAmount = none := by
  unfold canonical at hcanonical
  rw [hvariant] at hcanonical
  obtain ⟨hrecipient, hwithdrawal, _⟩ := hcanonical
  obtain ⟨recipient, h⟩ := Option.isSome_iff_exists.mp hrecipient
  exact ⟨recipient, h, hwithdrawal⟩

theorem withdrawal_shape (pub : Public K)
    (hvariant : pub.variant = .withdrawal) (hcanonical : canonical pub) :
    ∃ amount, amount ≠ 0 ∧ pub.withdrawalAmount = some amount ∧ pub.recipient = none := by
  unfold canonical at hcanonical
  rw [hvariant] at hcanonical
  obtain ⟨hrecipient, hamount, hnonzero, _⟩ := hcanonical
  obtain ⟨amount, h⟩ := Option.isSome_iff_exists.mp hamount
  have hne : amount ≠ 0 := by
    intro hz
    apply hnonzero
    simp [h, hz]
  exact ⟨amount, hne, h, Option.isNone_iff_eq_none.mp hrecipient⟩

/-- PIN2: a canonical private transfer carries no destination. -/
theorem private_transfer_destination (pub : Public K)
    (hvariant : pub.variant = .privateTransfer) (hcanonical : canonical pub) :
    pub.destination = none := by
  unfold canonical at hcanonical
  rw [hvariant] at hcanonical
  exact hcanonical.2.2.1

/-- PIN2: a canonical withdrawal carries a 32-byte destination. -/
theorem withdrawal_destination (pub : Public K)
    (hvariant : pub.variant = .withdrawal) (hcanonical : canonical pub) :
    ∃ d, pub.destination = some d ∧ d.length = 32 := by
  unfold canonical at hcanonical
  rw [hvariant] at hcanonical
  obtain ⟨_, _, _, hdest, _, _, hlen⟩ := hcanonical
  obtain ⟨d, h⟩ := Option.isSome_iff_exists.mp hdest
  exact ⟨d, h, hlen d h⟩

/-- PIN2: every canonical record has 32-byte pool and deployment-domain fields. -/
theorem canonical_bindingLengths (pub : Public K) (hcanonical : canonical pub) :
    bindingLengths pub := by
  unfold canonical at hcanonical
  cases hv : pub.variant <;> rw [hv] at hcanonical
  · exact hcanonical.2.2.2
  · exact hcanonical.2.2.2.2

/-- PIN2: the updated-record lemmas keep the binding suffix of `pub`; the
transfer form clears the destination, the withdrawal form takes a new one. -/
theorem private_transfer_updated_canonical (pub : Public K) (recipient : Digest K)
    (hpool : pub.pool.length = 32) (hdomain : pub.deploymentDomain.length = 32) :
    canonical {
      variant := .privateTransfer
      anchor := pub.anchor
      nullifier := pub.nullifier
      assetId := pub.assetId
      recipient := some recipient
      change := pub.change
      withdrawalAmount := none
      nextPairIndex := pub.nextPairIndex
      snapshotFrontier := pub.snapshotFrontier
      nextRoot := pub.nextRoot
      nextFrontier := pub.nextFrontier
      pool := pub.pool
      deploymentDomain := pub.deploymentDomain
      destination := none
    } := by
  simp [canonical, bindingLengths, hpool, hdomain]

theorem withdrawal_updated_canonical (pub : Public K) (amount : K) (hamount : amount ≠ 0)
    (destination : List (Fin 256)) (hdest : destination.length = 32)
    (hpool : pub.pool.length = 32) (hdomain : pub.deploymentDomain.length = 32) :
    canonical {
      variant := .withdrawal
      anchor := pub.anchor
      nullifier := pub.nullifier
      assetId := pub.assetId
      recipient := none
      change := pub.change
      withdrawalAmount := some amount
      nextPairIndex := pub.nextPairIndex
      snapshotFrontier := pub.snapshotFrontier
      nextRoot := pub.nextRoot
      nextFrontier := pub.nextFrontier
      pool := pub.pool
      deploymentDomain := pub.deploymentDomain
      destination := some destination
    } := by
  simp [canonical, bindingLengths, hamount, hdest, hpool, hdomain]

#print axioms bindingLengthsCheck_eq_true_iff
#print axioms check_eq_true_iff
#print axioms private_transfer_shape
#print axioms withdrawal_shape
#print axioms private_transfer_destination
#print axioms withdrawal_destination
#print axioms canonical_bindingLengths
#print axioms private_transfer_updated_canonical
#print axioms withdrawal_updated_canonical

end AspisR1.PublicOptionShape
