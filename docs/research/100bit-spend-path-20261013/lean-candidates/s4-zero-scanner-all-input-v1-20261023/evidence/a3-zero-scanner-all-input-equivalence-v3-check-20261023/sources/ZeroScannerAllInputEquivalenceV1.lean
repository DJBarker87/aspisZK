import ZeroScannerSourceStepsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1ZeroScannerAllInputEquivalenceV1
open AspisR1ZeroScannerSdkV1 AspisR1ZeroScannerSourceStepsV1

theorem tail_loop_total_exact (s : Slice U8) :
    tail.require_zero_loop s=.ok (scanList s.val) := by
  have main : ∀ xs : List U8, ∀ s : Slice U8, s.val=xs →
      tail.require_zero_loop s=.ok (scanList xs) := by
    intro xs
    induction xs with
    | nil =>
      intro s hs
      rw [tail.require_zero_loop,Aeneas.Std.loop.eq_def,tail_body_empty s hs]
      rfl
    | cons b bs ih =>
      intro s hs
      rw [tail.require_zero_loop,Aeneas.Std.loop.eq_def,tail_body_cons s b bs hs]
      by_cases hb : b=0#u8
      · simpa only [if_pos hb,scanList,tail.require_zero_loop] using ih (s.drop 1#usize) (tail_drop_cons s b bs hs)
      · simp only [if_neg hb,scanList]
  exact main s.val s rfl

theorem indexed_loop_total_exact (s : Slice U8) (index : Usize)
    (hib : index.val ≤ s.val.length) :
    indexed.require_zero_loop s index=.ok (scanList (s.val.drop index.val)) := by
  have main : ∀ fuel : Nat, ∀ index : Usize,
      s.val.length-index.val=fuel → index.val ≤ s.val.length →
      indexed.require_zero_loop s index=.ok (scanList (s.val.drop index.val)) := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro index hf hib
      by_cases hi : index.val<s.val.length
      · let b := s.val[index.val]'hi
        have hget : s.val[index.val]?=some b := List.getElem?_eq_getElem hi
        obtain ⟨next,hnext,hbody⟩ := indexed_body_step s index b hi hget
        have hnb : next.val ≤ s.val.length := by omega
        have hdec : s.val.length-next.val<fuel := by omega
        have hrec := ih (s.val.length-next.val) hdec next rfl hnb
        have hlist : s.val.drop index.val=b::s.val.drop next.val := by
          rw [hnext]
          exact drop_cons_at s.val index.val hi
        rw [hlist,scanList,indexed.require_zero_loop,Aeneas.Std.loop.eq_def,hbody]
        by_cases hb : b=0#u8
        · simpa only [if_pos hb,indexed.require_zero_loop] using hrec
        · simp only [if_neg hb]
      · have he : index.val=s.val.length := by omega
        rw [indexed.require_zero_loop,Aeneas.Std.loop.eq_def,
          indexed_body_done s index (by omega)]
        simp only [he,List.drop_length,scanList]
  exact main (s.val.length-index.val) index rfl hib

theorem indexed_total_exact (s : Slice U8) :
    indexed.require_zero s=.ok (scanList s.val) := by
  have hz : (0#usize).val=0 := rfl
  simpa only [indexed.require_zero,hz,List.drop_zero] using
    indexed_loop_total_exact s 0#usize (by change 0 ≤ s.val.length; omega)

theorem tail_total_exact (s : Slice U8) :
    tail.require_zero s=.ok (scanList s.val) := tail_loop_total_exact s

/-- Total source equality for every valid immutable byte slice, including
rejected inputs; no successful-execution premise is required. -/
theorem all_input_source_equivalence (s : Slice U8) :
    indexed.require_zero s=tail.require_zero s := by
  rw [indexed_total_exact,tail_total_exact]

theorem all_input_entry_equivalence (s : Slice U8) :
    indexed.entry s=tail.entry s := by
  exact all_input_source_equivalence s

theorem scanList_ok_iff (xs : List U8) :
    scanList xs=.Ok () ↔ ∀ b ∈ xs, b=0#u8 := by
  induction xs with
  | nil => simp [scanList]
  | cons b bs ih =>
    by_cases hb : b=0#u8
    · simp [scanList,hb,ih]
    · simp [scanList,hb,rejected]

theorem scanList_rejected_iff (xs : List U8) :
    scanList xs=rejected ↔ ∃ b ∈ xs, b≠0#u8 := by
  induction xs with
  | nil => simp [scanList,rejected]
  | cons b bs ih =>
    by_cases hb : b=0#u8
    · simp [scanList,hb,ih]
    · rw [scanList,if_neg hb]
      constructor
      · intro _
        exact ⟨b,by exact List.mem_cons_self ..,hb⟩
      · intro _
        rfl

theorem actual_acceptance_iff (s : Slice U8) :
    tail.require_zero s=.ok (.Ok ()) ↔ ∀ b ∈ s.val, b=0#u8 := by
  rw [tail_total_exact]
  simpa only [Result.ok.injEq] using scanList_ok_iff s.val

theorem actual_rejection_iff (s : Slice U8) :
    tail.require_zero s=.ok (.Err solana_program_error.ProgramError.AccountAlreadyInitialized) ↔
      ∃ b ∈ s.val, b≠0#u8 := by
  rw [tail_total_exact]
  simpa only [Result.ok.injEq,rejected] using scanList_rejected_iff s.val

theorem empty_slice_succeeds (s : Slice U8) (hs : s.val=[]) :
    indexed.require_zero s=.ok (.Ok ()) ∧ tail.require_zero s=.ok (.Ok ()) := by
  rw [indexed_total_exact,tail_total_exact,hs]
  exact ⟨rfl,rfl⟩

/-- In particular every nonzero position is rejected, with the exact SDK
error, without a mask/fixture or a length bound below the native slice bound. -/
theorem every_nonzero_position_rejected (s : Slice U8) (n : Nat) (hn : n<s.val.length)
    (hbyte : s.val[n]≠0#u8) :
    indexed.require_zero s=.ok rejected ∧ tail.require_zero s=.ok rejected := by
  have hm : ∃ b ∈ s.val, b≠0#u8 := ⟨s.val[n],List.getElem_mem hn,hbyte⟩
  have h := (scanList_rejected_iff s.val).mpr hm
  rw [indexed_total_exact,tail_total_exact,h]
  exact ⟨rfl,rfl⟩

#print axioms tail_loop_total_exact
#print axioms indexed_loop_total_exact
#print axioms all_input_source_equivalence
#print axioms actual_acceptance_iff
#print axioms actual_rejection_iff
#print axioms empty_slice_succeeds
#print axioms every_nonzero_position_rejected
end AspisR1ZeroScannerAllInputEquivalenceV1
