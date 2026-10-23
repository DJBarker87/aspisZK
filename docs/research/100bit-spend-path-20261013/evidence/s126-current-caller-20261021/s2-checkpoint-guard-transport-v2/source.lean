import S2OwnedCheckpointScanTotalV1

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.CheckpointGuardTransport

/-- Sequence interpretation of the pinned std Iter<u8>::any body, including
short circuit. Representation of an SDK iterator is a separate Kani boundary. -/
def stdAny : List U8 → Bool
  | [] => false
  | byte :: rest => if byte = 0#u8 then stdAny rest else true

theorem stdAny_false (bytes : List U8) :
    stdAny bytes = false ↔ ∀ byte ∈ bytes, byte = 0#u8 := by
  induction bytes with
  | nil => simp [stdAny]
  | cons byte rest ih =>
    by_cases h : byte = 0#u8
    · simp [stdAny, h, ih]
    · simp [stdAny, h]

theorem indexed_zero (bytes : alloc.vec.Vec U8) :
    (∀ byte ∈ bytes.val, byte = 0#u8) ↔
      ∀ j, j < bytes.val.length → S2OwnedCheckpointScanTotalV1.ZeroAt bytes j := by
  constructor
  · intro h j hj
    unfold S2OwnedCheckpointScanTotalV1.ZeroAt
    rw [List.getElem?_eq_getElem hj, h _ (List.getElem_mem hj)]
  · intro h byte hb
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hb
    have he := h j hj
    unfold S2OwnedCheckpointScanTotalV1.ZeroAt at he
    rw [List.getElem?_eq_getElem hj] at he
    exact Option.some.inj he

/-- TOTAL equality, without a traversal-success or zero-buffer premise. -/
theorem owned_eq_std (bytes : alloc.vec.Vec U8) :
    owned_checkpoint_nonzero bytes = ok (stdAny bytes.val) := by
  obtain ⟨out,hrun,hzero⟩ := S2OwnedCheckpointScanTotalV1.scan_total bytes
  have he : out = false ↔ stdAny bytes.val = false :=
    hzero.trans ((indexed_zero bytes).symm.trans (stdAny_false bytes.val).symm)
  have ho : out = stdAny bytes.val := by
    cases out <;> cases hstd : stdAny bytes.val <;> simp_all
  simpa only [ho] using hrun

/-- Contextual replacement preserves the complete result and arbitrary state
or trace carrier in A. Reject/continue computations are not simplified, and
may themselves fail or diverge. This is an owned-reference transport theorem;
it does not supply the actual SDK-to-sequence iterator instance. -/
theorem guard_eq {A : Type} (bytes : alloc.vec.Vec U8)
    (reject resume : Result A) :
    (do let nonzero ← owned_checkpoint_nonzero bytes
        if nonzero then reject else resume) =
      (if stdAny bytes.val then reject else resume) := by
  rw [owned_eq_std]
  rfl

#print axioms stdAny_false
#print axioms indexed_zero
#print axioms owned_eq_std
#print axioms guard_eq
end AspisS2OwnedStage1.CheckpointGuardTransport
