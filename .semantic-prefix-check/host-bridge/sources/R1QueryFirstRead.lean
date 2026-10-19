import R1DuplexSeek
import R1DuplexPrefixTable
import R1QuerySelectedPrefix
import R1QueryCompletion

/-! Deterministic query recovery at the first read of a following endpoint.
Only the selected advance prefix is recovered from the preceding table;
unused tail advances need not be present there. Missing squeeze values are
explicitly completed with oracle-consistent values. No completion law or
full Fiat--Shamir instance is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryFirstRead
open FS FS2 FS2.Duplex R0C.V3 QueryStateList
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

def result (p : Params M Cv L) (H : Addr L → State) (s : Nat → State) :=
  Q22.scanOut 8 Q22.q0 (blocks p H s 8) (advances s 8) (s 0)

theorem recover_query_before_endpoint (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State)
    (hstep : ∀ j < 8, s (j + 1) = H (advanceA p (s j)))
    (hread : ∀ j < 8, Read tr (advanceA p (s j)))
    (a c : Addr L) (haread : Read tr a) (hcread : Read tr c)
    (hparse : (parseAbsorb a).isSome) (hroot : s 0 = H a)
    (hprefix : c.toBytes.take 32 = bytes (result p H s).2) :
    ∃ k : Nat, k < 8 ∧ (result p H s).2 = s (k + 1) ∧
      DuplexSeek.seek p (tableBefore emptyTable tr c) 9 (result p H s).2 =
        some (a, states s (k + 1)) ∧
      ∀ acc : Addr L → State,
        (∀ j < k + 1, tableBefore emptyTable tr c (squeezeA p (s j)) = none →
          acc (squeezeA p (s j)) = H (squeezeA p (s j))) →
        QueryCompletion.complete p (tableBefore emptyTable tr c) acc (states s (k + 1)) =
          result p H s := by
  have hm : (result p H s).2 ∈ advances s 8 :=
    QueryContinuation.eight_pair_continuation (blocks p H s 8) (advances s 8) (s 0)
      (by simp [blocks]) (by simp [advances])
  obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm
  have hk8 : k < 8 := List.mem_range.mp hk
  have hselected : (result p H s).2 = s (k + 1) := heq.symm
  have hbefore : c.toBytes.take 32 = bytes (s (k + 1)) := by
    rw [← hselected]
    exact hprefix
  have hsteps : ∀ j < k + 1, s (j + 1) = H (advanceA p (s j)) :=
    fun j hj => hstep j (by omega)
  have hreads : ∀ j < k + 1, Read tr (advanceA p (s j)) :=
    fun j hj => hread j (by omega)
  have hcells := DuplexPrefixTable.table_cells p H tr Qtot hcons hQ hcoll s (k + 1)
    hsteps hreads c a hcread haread hbefore hroot
  have htable : ∀ b v, tableBefore emptyTable tr c b = some v → v = H b ∧ Read tr b :=
    DuplexPrefixTable.table_consistent H tr hcons c
  have hseek := DuplexSeek.seek_of_noColl p (tableBefore emptyTable tr c) H tr Qtot
    (k + 1) 9 hcons hQ hcoll htable s a hparse hroot hcells.1 hsteps hcells.2 (by omega)
  refine ⟨k, hk8, hselected, ?_, ?_⟩
  · rw [hselected]
    exact hseek
  · intro acc hmissing
    rw [QueryCompletion.complete_states p (tableBefore emptyTable tr c) acc H s (k + 1)
      (by
        intro j hj
        exact QueryCompletion.getter_correct (tableBefore emptyTable tr c) acc H
          (squeezeA p (s j)) (fun b v hb => (htable b v hb).1) (hmissing j hj))]
    have hx := advances_nodup p H tr Qtot hcons hQ hcoll s 8 hstep hread
    have hlen : (advances s 8).length = 8 := by simp [advances]
    have hkxs : k < (advances s 8).length := by omega
    have hsel : (Q22.scanOut 8 Q22.q0 (blocks p H s 8) (advances s 8) (s 0)).2 =
        (advances s 8)[k]'hkxs := by
      simpa only [result, advances, List.getElem_map, List.getElem_range] using hselected
    have htrunc := QuerySelectedPrefix.selected_truncate (blocks p H s 8) (advances s 8)
      (s 0) k hx hlen hkxs hsel
    simpa only [blocks_take p H s 8 (k + 1) (by omega),
      advances_take s 8 (k + 1) (by omega), result] using htrunc

#print axioms recover_query_before_endpoint
end AspisR1.QueryFirstRead
end
