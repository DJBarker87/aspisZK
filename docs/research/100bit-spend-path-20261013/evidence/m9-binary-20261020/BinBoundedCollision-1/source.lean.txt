import RawBoundedTrace
import BinRawByteCollisionTargets
import RawBoundedCollision
import TraceBadWitness

/-! The single unrestricted-byte collision event implies both legacy
decoder collision exclusions on the canonical restricted trace. This is
deterministic reuse only; the event probability remains on raw bytes. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.BinBoundedCollision

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RawBoundedCollision (read_trace lookup_before current_or_before)

theorem no_duplex_collision {M Cv : Type} {L : Nat} (p : Params M Cv L)
    (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad p.iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr) :
    ¬ hitsBad (badColl p Q) emptyTable (RawBoundedTrace.trace L tr) := by
  apply TraceBadWitness.not_hitsBad (badColl p Q) (fun a : Addr L => H a.toBytes)
    (RawBoundedTrace.trace L tr) (RawBoundedTrace.trace_consistent L H tr hcons)
  intro a ha hbad
  obtain ⟨hcan,hraw⟩ := (read_trace L tr a).1 ha
  have hgood := AllAddressCollisionTrace.outside_at_read p.iv BinRawByteCollisionTargets.pred
    H tr Q hcons hQ hout a.toBytes hraw
  rcases hbad.2 with hiv | hprev | hprefix
  · exact hgood.1 hiv
  · obtain ⟨b,hb⟩ := hprev
    obtain ⟨hbefore, he⟩ := lookup_before L H tr hcons a b hcan _ hb
    exact hgood.2.1 b.toBytes hbefore he.symm
  · obtain ⟨b,hb,hpre⟩ := hprefix
    have hp : BinRawByteCollisionTargets.pred 4 b.toBytes = some (H a.toBytes) := by
      rw [BinRawByteCollisionTargets.pred_prefix]
      exact BinRawByteCollisionTargets.prefix_of_take b.toBytes (H a.toBytes) hpre
    exact hgood.2.2 4 b.toBytes (current_or_before L H tr hcons a b hcan hb) hp

theorem no_parsed_collision {L : Nat} (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (j : Fin 5) (f : Addr L → Option State)
    (hf : ∀ a, f a = BinRawByteCollisionTargets.pred j a.toBytes) :
    ¬ hitsBad (ParsedStateCollision.bad f Q) emptyTable (RawBoundedTrace.trace L tr) := by
  apply TraceBadWitness.not_hitsBad (ParsedStateCollision.bad f Q)
    (fun a : Addr L => H a.toBytes) (RawBoundedTrace.trace L tr)
    (RawBoundedTrace.trace_consistent L H tr hcons)
  intro a ha hbad
  obtain ⟨hcan,hraw⟩ := (read_trace L tr a).1 ha
  have hgood := AllAddressCollisionTrace.outside_at_read iv BinRawByteCollisionTargets.pred
    H tr Q hcons hQ hout a.toBytes hraw
  obtain ⟨b,hb,hpred⟩ := hbad.2
  rw [hf] at hpred
  exact hgood.2.2 j b.toBytes (current_or_before L H tr hcons a b hcan hb) hpred

theorem no_tail_collision {L : Nat} (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr) :
    ¬ hitsBad (ParsedStateCollision.bad (TrailingStateFrame.tailState (L := L)) Q)
      emptyTable (RawBoundedTrace.trace L tr) := by
  apply no_parsed_collision iv H tr Q hcons hQ hout 2
  intro a
  rw [BinRawByteCollisionTargets.pred_tail]
  rfl

#print axioms no_duplex_collision
#print axioms no_parsed_collision
#print axioms no_tail_collision
end AspisR1.BinBoundedCollision
end
