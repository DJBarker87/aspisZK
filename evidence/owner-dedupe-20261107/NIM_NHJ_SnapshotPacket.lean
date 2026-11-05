import NHJ_EntryDomains
import NIM_NHJ_SnapshotAssociation
import NHJ_SdkDomains
set_option autoImplicit false
noncomputable section
namespace NHJ_SnapshotPacket
open Aeneas Aeneas.Std Result
open AspisR1.S2W_D189Entry AspisR1.S2W_D189Wrappers AspisR1.S2Trust

/-- Complete reference-to-actual-entry value join. No returned-value or parent
acceptance premise is used. Native call association is the separate P6 packet. -/
theorem cohort_return (e : Entry) (a : Nat) (l1 l2 : Usize) :
    let old := (e.records (e.handles a).1).owned
    (do let returned ← NHJ_SnapshotReference.snapshot_ref old.key old.owner
          old.is_signer old.is_writable old.executable l1 l2
          (.Ok (e.buffers (e.handles a).1))
        ok (NHJ_SnapshotAssociation.port returned)) =
      ok (e.snapshot a l1.val l2.val) := by
  dsimp only
  rw [NHJ_SnapshotAssociation.source]
  · exact NHJ_SnapshotEntry.source e a l1 l2
  · intro error impossible
    cases impossible

theorem caller_domains (e : Entry) :
    (∀ a, NGL_StorageCases.Domain (e.snapshot a (firstSizes a).1 (firstSizes a).2)) ∧
    (∀ a, NGL_StorageCases.Domain (e.snapshot a (secondSizes a).1 (secondSizes a).2)) :=
  ⟨NHJ_EntryDomains.first_table e,NHJ_EntryDomains.second_table e⟩

/-- Exhaustive legal shared-borrow bracket, including existing guards and
external counts. Fresh logical names and the success/error partition are
proved; no zero counter or successful borrow is an input. -/
theorem bracket_all {W F : Type} (L : Library W F) (sdk : S2TrustedSdkBorrow L)
    (w : W) (s : Heap F) (related : L.related w s) (valid : Valid s)
    (account : Nat) (live : s.ownerLive account = true) :
    ∃ token owner,
      (∃ w1 w2 w3,
        L.run w (.shared account token owner) = (w1,.guard token) ∧
        L.run w1 (.deref token) = (w2,.payload (s.payload (s.accounts account).1)) ∧
        L.run w2 (.drop token) = (w3,.unit) ∧ L.related w3 s) ∨
      (∃ w', L.run w (.shared account token owner) = (w',.borrowFailed) ∧ L.related w' s) := by
  obtain ⟨token,owner,enabled⟩ := NHJ_SdkDomains.enabled_exists s account live
  refine ⟨token,owner,?_⟩
  rcases NHJ_SdkDomains.counter_cases s valid account with ⟨low,high⟩ | blocked
  · exact Or.inl (NHJ_SdkBorrowPacket.returning_shared L sdk w s related valid account token owner enabled low high)
  · exact Or.inr (NHJ_SdkBorrowPacket.rejected_shared L sdk w s related valid account token owner enabled blocked)
#print axioms cohort_return
#print axioms caller_domains
#print axioms bracket_all
end NHJ_SnapshotPacket
