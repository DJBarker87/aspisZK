import AllAddressCollisionTrace

/-! An oracle program can retain its own complete query/answer log without
making any additional oracle calls. Replaying already-read verifier cells
does not increase the distinct-first-read budget. These are operational facts
for constructing the commitment-word compiler, not an extraction theorem. -/
set_option autoImplicit false
namespace AspisR1.OracleProgramRecording

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw

variable {I A O : Type} [DecidableEq I]

def record : Program I A O → Program I A (View I A O)
  | .done out => .done ([], out)
  | .ask a next => .ask a fun f =>
      bind (record (next f)) fun v => .done ((a, f) :: v.1, v.2)

theorem eval_record (H : I → A) (p : Program I A O) :
    eval H (record p) = ((eval H p).1, eval H p) := by
  induction p with
  | done out => rfl
  | ask a next ih =>
      simp only [record, eval, eval_bind, ih]
      simp

theorem firstReads_append_reused [Fintype A] [Inhabited A]
    (tr replay : List (I × A))
    (hread : ∀ a, Read replay a → Read tr a) :
    firstReads emptyTable (tr ++ replay) = firstReads emptyTable tr := by
  classical
  have hsub : (replay.map Prod.fst).toFinset ⊆ (tr.map Prod.fst).toFinset := by
    intro a ha
    exact List.mem_toFinset.mpr (hread a (List.mem_toFinset.mp ha))
  rw [AllAddressCollisionTrace.firstReads_eq_card_finiteSupport,
    AllAddressCollisionTrace.firstReads_eq_card_finiteSupport]
  simp only [List.map_append, List.toFinset_append, Finset.union_eq_left.mpr hsub]

theorem firstReads_repeat_suffix [Fintype A] [Inhabited A]
    (pre tail : List (I × A)) :
    firstReads emptyTable ((pre ++ tail) ++ tail) = firstReads emptyTable (pre ++ tail) := by
  apply firstReads_append_reused
  intro a ha
  change a ∈ (pre ++ tail).map Prod.fst
  rw [List.map_append]
  exact List.mem_append.mpr (Or.inr ha)

/-- Appending already-known cells does not move the first read of an address
already present in the original trace. -/
theorem firstIdx_append_of_read (a : I) (tr tail : List (I × A))
    (ha : Read tr a) : firstIdx a (tr ++ tail) = firstIdx a tr := by
  induction tr with
  | nil => simp [Read] at ha
  | cons q rest ih =>
      rcases q with ⟨i, v⟩
      simp only [Read, List.map_cons, List.mem_cons] at ha
      by_cases h : i = a
      · simp [firstIdx, h]
      · have hr : Read rest a := ha.resolve_left (Ne.symm h)
        simp [firstIdx, h, ih hr]

theorem cut_append_of_read (a : I) (tr tail : List (I × A))
    (ha : Read tr a) :
    (tr ++ tail).take (firstIdx a (tr ++ tail)) = tr.take (firstIdx a tr) := by
  rw [firstIdx_append_of_read a tr tail ha]
  exact List.take_append_of_le_length (Nat.le_of_lt (firstIdx_lt_length a tr ha))

#print axioms eval_record
#print axioms firstReads_append_reused
#print axioms firstReads_repeat_suffix
#print axioms firstIdx_append_of_read
#print axioms cut_append_of_read
end AspisR1.OracleProgramRecording
