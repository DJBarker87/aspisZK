import R1AppendPath
import R1AppendPair
import R1SpendSemantics

/-! Deterministic note and literal append-path facts from production gates.
Non-carry frontier cells are a separate public-prevalidation premise. The
table recurrence, chronological frontier invariant, actual public codec and
verifier source, shared-oracle law, and privacy remain outside this result. -/
set_option autoImplicit false
namespace AspisR1.AppendSemantics
open R0P
variable {K : Type} [Field K]

/-- The frontier portion of the host's public `validate_transition` guard.
It contains neither the root nor the carry-node equality proved by the gates. -/
def NonCarryShape (pub : Public K) : Prop :=
  ∀ level : Fin 20, level.val ≠ digestCarry pub.nextPairIndex →
    pub.nextFrontier level =
      if level.val < digestCarry pub.nextPairIndex ∨ digestBitZero pub level
      then AppendNode.frozenEmpty level.castSucc else pub.snapshotFrontier level

def expectedFrontier (pub : Public K) (pair : Digest K) (level : Fin 20) : Digest K :=
  if level.val = digestCarry pub.nextPairIndex
  then AppendPath.pathPrefix pub pair level.val
  else if level.val < digestCarry pub.nextPairIndex ∨ digestBitZero pub level
  then AppendNode.frozenEmpty level.castSucc else pub.snapshotFrontier level

theorem complete_frontier (prime : Nat) [CharP K prime] (hprime : prime = 2^31-1)
    (pub : Public K) (A : Trace K) (hs : Holds scheduleFamily pub A)
    (hd : Holds digestFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) (hshape : NonCarryShape pub) :
    pub.nextFrontier = expectedFrontier pub (OutputNotes.output A 33) := by
  funext level
  unfold expectedFrontier
  by_cases he : level.val = digestCarry pub.nextPairIndex
  · rw [if_pos he]
    have hc : digestCarry pub.nextPairIndex < 20 := by omega
    have hi : level = ⟨digestCarry pub.nextPairIndex, hc⟩ := Fin.ext he
    rw [hi]
    exact AppendPath.next_frontier_carry prime hprime pub A hs hd hpo hb hc
  · rw [if_neg he]
    exact hshape level he

structure GateFacts (pub : Public K) (A : Trace K) : Prop where
  notes : SpendSemantics.NoteFacts pub A
  pairValid : (AppendPair.leaf A).Valid
  root : pub.nextRoot = AppendPath.pathPrefix pub (OutputNotes.output A 33) 20
  carry : ∀ hc : digestCarry pub.nextPairIndex < 20,
    pub.nextFrontier ⟨digestCarry pub.nextPairIndex, hc⟩ =
      AppendPath.pathPrefix pub (OutputNotes.output A 33) (digestCarry pub.nextPairIndex)
  transferPair : pub.variant = .privateTransfer → ∀ recipient : Digest K,
    pub.recipient = some recipient → OutputNotes.output A 33 = nodeCompress recipient pub.change
  withdrawalPair : pub.variant = .withdrawal →
    OutputNotes.output A 33 = nodeCompress pub.change (fun _ => 0)

theorem of_production (prime : Nat) [CharP K prime] (hprime : prime = 2^31-1)
    (pub : Public K) (A : Trace K) (lam chi : K)
    (h : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A) : GateFacts pub A := by
  have ho : Holds occupancyFamily pub A := h.1.2.1
  have hs : Holds scheduleFamily pub A := h.1.2.2.2.1
  have hd : Holds digestFamily pub A := h.1.2.2.2.2.2.1
  have hpo : Holds poseidonScalarFamily pub A := h.1.2.2.2.2.2.2.1
  exact ⟨SpendSemantics.of_production prime hprime pub A lam chi h,
    AppendPair.leaf_valid pub A ho,
    AppendPath.next_root prime hprime pub A hs hd hpo h.2,
    AppendPath.next_frontier_carry prime hprime pub A hs hd hpo h.2,
    fun hv recipient hp => AppendPair.transfer_output pub A hs hpo h.2 hd hv recipient hp,
    fun hv => AppendPair.withdrawal_output pub A hs hpo h.2 hd ho hv⟩

/-- Full literal public root/frontier binding, retaining the host-precheck
premise and allowing carry=20 at the last insertion. It is not yet a theorem
equating this recurrence to a chronological Merkle tree. -/
theorem afterstate_of_production (prime : Nat) [CharP K prime]
    (hprime : prime = 2^31-1) (pub : Public K) (A : Trace K) (lam chi : K)
    (h : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A)
    (hshape : NonCarryShape pub) :
    GateFacts pub A ∧ pub.nextFrontier = expectedFrontier pub (OutputNotes.output A 33) := by
  exact ⟨of_production prime hprime pub A lam chi h,
    complete_frontier prime hprime pub A h.1.2.2.2.1 h.1.2.2.2.2.2.1
      h.1.2.2.2.2.2.2.1 h.2 hshape⟩

#print axioms complete_frontier
#print axioms of_production
#print axioms afterstate_of_production
end AspisR1.AppendSemantics
