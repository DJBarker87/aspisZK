import R0P.Core

/-! A small executable predicate for the option/variant shape represented by
`R0P.Public`. This does not parse Rust bytes and does not impose value bounds. -/
set_option autoImplicit false

namespace AspisR1.PublicOptionShape

open R0P

variable {K : Type} [Field K] [DecidableEq K]

def canonical (pub : Public K) : Prop :=
  match pub.variant with
  | .privateTransfer => pub.recipient.isSome = true ∧ pub.withdrawalAmount = none
  | .withdrawal => pub.recipient.isNone = true ∧ pub.withdrawalAmount.isSome = true ∧
      pub.withdrawalAmount ≠ some 0

def check (pub : Public K) : Bool :=
  match pub.variant with
  | .privateTransfer => pub.recipient.isSome && pub.withdrawalAmount.isNone
  | .withdrawal => pub.recipient.isNone && pub.withdrawalAmount.isSome &&
      pub.withdrawalAmount != some 0

theorem check_eq_true_iff (pub : Public K) : check pub = true ↔ canonical pub := by
  cases hv : pub.variant <;> simp [check, canonical, hv, and_assoc]

theorem private_transfer_shape (pub : Public K)
    (hvariant : pub.variant = .privateTransfer) (hcanonical : canonical pub) :
    ∃ recipient, pub.recipient = some recipient ∧ pub.withdrawalAmount = none := by
  unfold canonical at hcanonical
  rw [hvariant] at hcanonical
  obtain ⟨hrecipient, hwithdrawal⟩ := hcanonical
  obtain ⟨recipient, h⟩ := Option.isSome_iff_exists.mp hrecipient
  exact ⟨recipient, h, hwithdrawal⟩

theorem withdrawal_shape (pub : Public K)
    (hvariant : pub.variant = .withdrawal) (hcanonical : canonical pub) :
    ∃ amount, amount ≠ 0 ∧ pub.withdrawalAmount = some amount ∧ pub.recipient = none := by
  unfold canonical at hcanonical
  rw [hvariant] at hcanonical
  obtain ⟨hrecipient, hamount, hnonzero⟩ := hcanonical
  obtain ⟨amount, h⟩ := Option.isSome_iff_exists.mp hamount
  have hne : amount ≠ 0 := by
    intro hz
    apply hnonzero
    simp [h, hz]
  exact ⟨amount, hne, h, Option.isNone_iff_eq_none.mp hrecipient⟩

theorem private_transfer_updated_canonical (pub : Public K) (recipient : Digest K) :
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
    } := by
  simp [canonical]

theorem withdrawal_updated_canonical (pub : Public K) (amount : K) (hamount : amount ≠ 0) :
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
    } := by
  simp [canonical, hamount]

#print axioms check_eq_true_iff
#print axioms private_transfer_shape
#print axioms withdrawal_shape
#print axioms private_transfer_updated_canonical
#print axioms withdrawal_updated_canonical

end AspisR1.PublicOptionShape
