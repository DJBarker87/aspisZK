import RawBoundedTrace
import RawByteCollisionTargets
import TraceBadWitness

/-! The single unrestricted-byte collision event implies both legacy
decoder collision exclusions on the canonical restricted trace. This is
deterministic reuse only; the event probability remains on raw bytes. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawBoundedCollision

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem read_trace (L : Nat) {A : Type} (tr : List (Bytes × A)) (a : Addr L) :
    Read (RawBoundedTrace.trace L tr) a ↔
      CanonicalByteAddress.Canonical a ∧ Read tr a.toBytes := by
  simp only [Read, List.mem_map]
  constructor
  · rintro ⟨⟨b,v⟩, hmem, he⟩
    simp only [Prod.fst] at he
    subst b
    obtain ⟨hcan,hraw⟩ := (RawBoundedTrace.mem_trace L tr a v).1 hmem
    exact ⟨hcan, (a.toBytes,v), hraw, rfl⟩
  · rintro ⟨hcan, ⟨⟨input,v⟩, hmem, he⟩⟩
    simp only [Prod.fst] at he
    subst input
    exact ⟨(a,v), (RawBoundedTrace.mem_trace L tr a v).2 ⟨hcan,hmem⟩, rfl⟩

theorem lookup_before (L : Nat) (H : Bytes → State) (tr : List (Bytes × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (a b : Addr L)
    (ha : CanonicalByteAddress.Canonical a) (v : State)
    (hv : tableBefore emptyTable (RawBoundedTrace.trace L tr) a b = some v) :
    Before tr b.toBytes a.toBytes ∧ v = H b.toBytes := by
  have he := RawBoundedTrace.tableBefore_trace L emptyTable tr ⟨a,ha⟩
  rw [RawBoundedTrace.table_empty] at he
  rw [he] at hv
  change RawBoundedTrace.table L (tableBefore emptyTable tr a.toBytes) b = some v at hv
  have hb : CanonicalByteAddress.Canonical b := by
    by_contra hb
    rw [RawBoundedTrace.table_noncanonical L _ b hb] at hv
    cases hv
  rw [RawBoundedTrace.table_canonical L _ b hb,
    tableBefore_eq H tr emptyTable a.toBytes b.toBytes hcons] at hv
  have hbefore : Before tr b.toBytes a.toBytes := by
    by_contra hn
    simp [hn, emptyTable] at hv
  refine ⟨hbefore, ?_⟩
  rw [if_pos hbefore] at hv
  exact (Option.some.inj hv).symm

theorem current_or_before (L : Nat) (H : Bytes → State) (tr : List (Bytes × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (a b : Addr L)
    (ha : CanonicalByteAddress.Canonical a)
    (hb : b = a ∨ tableBefore emptyTable (RawBoundedTrace.trace L tr) a b ≠ none) :
    b.toBytes = a.toBytes ∨ Before tr b.toBytes a.toBytes := by
  rcases hb with rfl | hb
  · exact Or.inl rfl
  · right
    cases hv : tableBefore emptyTable (RawBoundedTrace.trace L tr) a b with
    | none => exact False.elim (hb hv)
    | some v => exact (lookup_before L H tr hcons a b ha v hv).1

theorem no_duplex_collision {M Cv : Type} {L : Nat} (p : Params M Cv L)
    (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad p.iv RawByteCollisionTargets.pred Q)
      emptyTable tr) :
    ¬ hitsBad (badColl p Q) emptyTable (RawBoundedTrace.trace L tr) := by
  apply TraceBadWitness.not_hitsBad (badColl p Q) (fun a : Addr L => H a.toBytes)
    (RawBoundedTrace.trace L tr) (RawBoundedTrace.trace_consistent L H tr hcons)
  intro a ha hbad
  obtain ⟨hcan,hraw⟩ := (read_trace L tr a).1 ha
  have hgood := AllAddressCollisionTrace.outside_at_read p.iv RawByteCollisionTargets.pred
    H tr Q hcons hQ hout a.toBytes hraw
  rcases hbad.2 with hiv | hprev | hprefix
  · exact hgood.1 hiv
  · obtain ⟨b,hb⟩ := hprev
    obtain ⟨hbefore, he⟩ := lookup_before L H tr hcons a b hcan _ hb
    exact hgood.2.1 b.toBytes hbefore he.symm
  · obtain ⟨b,hb,hpre⟩ := hprefix
    have hp : RawByteCollisionTargets.pred 10 b.toBytes = some (H a.toBytes) := by
      rw [RawByteCollisionTargets.pred_prefix]
      exact RawByteCollisionTargets.prefix_of_take b.toBytes (H a.toBytes) hpre
    exact hgood.2.2 10 b.toBytes (current_or_before L H tr hcons a b hcan hb) hp

theorem no_parsed_collision {L : Nat} (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable tr)
    (j : Fin 11) (f : Addr L → Option State)
    (hf : ∀ a, f a = RawByteCollisionTargets.pred j a.toBytes) :
    ¬ hitsBad (ParsedStateCollision.bad f Q) emptyTable (RawBoundedTrace.trace L tr) := by
  apply TraceBadWitness.not_hitsBad (ParsedStateCollision.bad f Q)
    (fun a : Addr L => H a.toBytes) (RawBoundedTrace.trace L tr)
    (RawBoundedTrace.trace_consistent L H tr hcons)
  intro a ha hbad
  obtain ⟨hcan,hraw⟩ := (read_trace L tr a).1 ha
  have hgood := AllAddressCollisionTrace.outside_at_read iv RawByteCollisionTargets.pred
    H tr Q hcons hQ hout a.toBytes hraw
  obtain ⟨b,hb,hpred⟩ := hbad.2
  rw [hf] at hpred
  exact hgood.2.2 j b.toBytes (current_or_before L H tr hcons a b hcan hb) hpred

theorem no_tail_collision {L : Nat} (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable tr) :
    ¬ hitsBad (ParsedStateCollision.bad (TrailingStateFrame.tailState (L := L)) Q)
      emptyTable (RawBoundedTrace.trace L tr) := by
  apply no_parsed_collision iv H tr Q hcons hQ hout 8
  intro a
  rw [RawByteCollisionTargets.pred_tail]
  rfl

#print axioms read_trace
#print axioms lookup_before
#print axioms current_or_before
#print axioms no_duplex_collision
#print axioms no_parsed_collision
#print axioms no_tail_collision
end AspisR1.RawBoundedCollision
end
