import R1QueryBackgroundChain
import R1DuplexPrefixTable
import R1TableStateSeparation

/-! No-collision trace facts for a query chain rooted at a read endpoint.
Only deterministic read/order consequences are proved here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryChainTraceFacts

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

private theorem chain_step (p : Params M Cv L) (H : Addr L → State)
    (c : Addr L) (j : Nat) :
    QuerySampler.state p H (H c) (j + 1) =
      H (advanceA p (QuerySampler.state p H (H c) j)) := rfl

theorem root_before (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (c : Addr L) (hc : Read tr c) (n : Nat)
    (hreads : ∀ k < n,
      Read tr (squeezeA p (QuerySampler.state p H (H c) k)) ∧
      Read tr (advanceA p (QuerySampler.state p H (H c) k))) :
    ∀ k < n,
      Before tr c (squeezeA p (QuerySampler.state p H (H c) k)) ∧
      Before tr c (advanceA p (QuerySampler.state p H (H c) k)) := by
  let s := QuerySampler.state p H (H c)
  have hstep : ∀ j < n, s (j + 1) = H (advanceA p (s j)) := by
    intro j hj
    rfl
  have hadj (j : Nat) (hj : j + 1 < n) :
      Before tr (advanceA p (s j)) (squeezeA p (s (j + 1))) ∧
      Before tr (advanceA p (s j)) (advanceA p (s (j + 1))) := by
    have hadv := (hreads j (by omega)).2
    have hsq := (hreads (j + 1) hj).1
    have hadv' := (hreads (j + 1) hj).2
    have hps : (squeezeA p (s (j + 1))).toBytes.take 32 =
        bytes (H (advanceA p (s j))) := by
      rw [toBytes_squeezeA]
      exact congrArg bytes (hstep j (by omega))
    have hpa : (advanceA p (s (j + 1))).toBytes.take 32 =
        bytes (H (advanceA p (s j))) := by
      rw [toBytes_advanceA]
      exact congrArg bytes (hstep j (by omega))
    exact ⟨noColl_prefix_after p Qtot H tr hcons hQ hcoll
        (advanceA p (s j)) (squeezeA p (s (j + 1))) hadv hsq hps,
      noColl_prefix_after p Qtot H tr hcons hQ hcoll
        (advanceA p (s j)) (advanceA p (s (j + 1))) hadv hadv' hpa⟩
  intro k
  induction k with
  | zero =>
      intro hk
      have hsq := (hreads 0 hk).1
      have hadv := (hreads 0 hk).2
      have hps : (squeezeA p (s 0)).toBytes.take 32 = bytes (H c) := by
        rw [toBytes_squeezeA]
        rfl
      have hpa : (advanceA p (s 0)).toBytes.take 32 = bytes (H c) := by
        rw [toBytes_advanceA]
        rfl
      exact ⟨noColl_prefix_after p Qtot H tr hcons hQ hcoll c
          (squeezeA p (s 0)) hc hsq hps,
        noColl_prefix_after p Qtot H tr hcons hQ hcoll c
          (advanceA p (s 0)) hc hadv hpa⟩
  | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hnext := hadj k hk
      exact ⟨before_trans tr hprev.2 hnext.1,
        before_trans tr hprev.2 hnext.2⟩

theorem advance_before (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (c : Addr L) (n : Nat)
    (hreads : ∀ k < n,
      Read tr (squeezeA p (QuerySampler.state p H (H c) k)) ∧
      Read tr (advanceA p (QuerySampler.state p H (H c) k))) :
    ∀ j k, j < k → k < n →
      Before tr (advanceA p (QuerySampler.state p H (H c) j))
        (squeezeA p (QuerySampler.state p H (H c) k)) ∧
      Before tr (advanceA p (QuerySampler.state p H (H c) j))
        (advanceA p (QuerySampler.state p H (H c) k)) := by
  let s := QuerySampler.state p H (H c)
  have hstep : ∀ j < n, s (j + 1) = H (advanceA p (s j)) := by
    intro j hj
    rfl
  have hadj (j : Nat) (hj : j + 1 < n) :
      Before tr (advanceA p (s j)) (squeezeA p (s (j + 1))) ∧
      Before tr (advanceA p (s j)) (advanceA p (s (j + 1))) := by
    have hadv := (hreads j (by omega)).2
    have hsq := (hreads (j + 1) hj).1
    have hadv' := (hreads (j + 1) hj).2
    have hps : (squeezeA p (s (j + 1))).toBytes.take 32 =
        bytes (H (advanceA p (s j))) := by
      rw [toBytes_squeezeA]
      exact congrArg bytes (hstep j (by omega))
    have hpa : (advanceA p (s (j + 1))).toBytes.take 32 =
        bytes (H (advanceA p (s j))) := by
      rw [toBytes_advanceA]
      exact congrArg bytes (hstep j (by omega))
    exact ⟨noColl_prefix_after p Qtot H tr hcons hQ hcoll
        (advanceA p (s j)) (squeezeA p (s (j + 1))) hadv hsq hps,
      noColl_prefix_after p Qtot H tr hcons hQ hcoll
        (advanceA p (s j)) (advanceA p (s (j + 1))) hadv hadv' hpa⟩
  intro j k hjk hk
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_or_ge j k with hjk' | hjEq
      · have hprev := ih j hjk' (by omega)
        have hnext := hadj k hk
        exact ⟨before_trans tr hprev.2 hnext.1,
          before_trans tr hprev.2 hnext.2⟩
      · have hjeq : j = k := by omega
        subst j
        exact hadj k hk

theorem states_ne (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (c : Addr L) (hc : Read tr c) (n : Nat)
    (hreads : ∀ k < n,
      Read tr (squeezeA p (QuerySampler.state p H (H c) k)) ∧
      Read tr (advanceA p (QuerySampler.state p H (H c) k))) :
    ∀ j k, j < k → k < n →
      QuerySampler.state p H (H c) j ≠ QuerySampler.state p H (H c) k := by
  have hbefore := root_before p H tr Qtot hcons hQ hcoll c hc n hreads
  have hadvBefore := advance_before p H tr Qtot hcons hQ hcoll c n hreads
  intro j k hjk hk
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hrk := (hreads k' (by omega)).2
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst j
    change H c ≠ H (advanceA p (QuerySampler.state p H (H c) k'))
    exact noColl_injective p Qtot H tr hcons hQ hcoll c
      (advanceA p (QuerySampler.state p H (H c) k')) hc hrk
      (before_ne tr (hbefore k' (by omega)).2)
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    change H (advanceA p (QuerySampler.state p H (H c) j')) ≠
      H (advanceA p (QuerySampler.state p H (H c) k'))
    exact noColl_injective p Qtot H tr hcons hQ hcoll
      (advanceA p (QuerySampler.state p H (H c) j'))
      (advanceA p (QuerySampler.state p H (H c) k'))
      (hreads j' (by omega)).2 hrk
      (before_ne tr (hadvBefore j' k' (by omega) (by omega)).2)

theorem known_ne_state (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (c : Addr L) (hc : Read tr c) (n : Nat)
    (hreads : ∀ k < n,
      Read tr (squeezeA p (QuerySampler.state p H (H c) k)) ∧
      Read tr (advanceA p (QuerySampler.state p H (H c) k)))
    (b : Addr L) (v : State)
    (hcell : tableBefore emptyTable tr c b = some v) :
    ∀ k < n, v ≠ QuerySampler.state p H (H c) k := by
  have hbefore := root_before p H tr Qtot hcons hQ hcoll c hc n hreads
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    exact TableStateSeparation.known_ne_endpoint p H tr Qtot hcons hQ hcoll
      c hc b v hcell
  · have hkpos : 0 < k := by omega
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨hv, hbRead⟩ := DuplexPrefixTable.table_consistent H tr hcons c b v hcell
    have hcadv := (hbefore k' (by omega)).2
    have hbadv : Before tr b (advanceA p (QuerySampler.state p H (H c) k')) := by
      have hbc : Before tr b c := by
        rw [tableBefore_eq H tr emptyTable c b hcons] at hcell
        split at hcell
        · assumption
        · simp [emptyTable] at hcell
      exact before_trans tr hbc hcadv
    have hbneq : b ≠ advanceA p (QuerySampler.state p H (H c) k') := before_ne tr hbadv
    have hne := noColl_injective p Qtot H tr hcons hQ hcoll b
      (advanceA p (QuerySampler.state p H (H c) k')) hbRead
      (hreads k' (by omega)).2 hbneq
    intro heq
    apply hne
    rw [← hv, heq, chain_step]

#print axioms root_before
#print axioms advance_before
#print axioms states_ne
#print axioms known_ne_state

end AspisR1.QueryChainTraceFacts
end
