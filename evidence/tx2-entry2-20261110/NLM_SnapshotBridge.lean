import NLM_RuntimeInput
set_option autoImplicit false
noncomputable section
namespace NLM_SnapshotBridge
open Aeneas Aeneas.Std AspisR1 AspisR1.S2W_D189Entry
open AspisR1.S2W_ReturnedCheckpoint NLF_ParentModel
/-- Source snapshot with its std acquire/deref/release trace. Allocation/copy
still needs the native snapshot window; this is not a native row packet. -/
def step (e : Entry) (prior : List Nat) (a lo hi : Nat) :=
 (NLF_SnapshotEvents.step (NLF_SnapshotFold.run (NLM_RuntimeInput.initial e) prior).1 a,
  e.snapshot a lo hi)
/-- No read-success premise: the SDK token reply itself is computed. -/
theorem borrowed (e : Entry) (prior : List Nat) (a lo hi : Nat) :
 ((step e prior a lo hi).1.2).map NLF_SdkModel.Payload.bytes =
 .ok (nativeBytes (e.buffers (e.handles a).1)) := by
 have h := NLF_SnapshotOccurrence.packet e.heap (NLM_RuntimeInput.records e)
  (NLM_RuntimeInput.money e) prior a
 dsimp only at h
 change ((NLF_SnapshotEvents.step _ _).2).map _ = _
 unfold NLM_RuntimeInput.initial
 rw [h.2.2.1]
 change Except.ok (NLF_RuntimeInterpretation.byteList e.heap (e.handles a).1) = _
 rw [NLM_RuntimeInput.payload_bytes]
/-- Deferred bad length is part of the returned owned value, after release. -/
theorem owned (e : Entry) (prior : List Nat) (a lo hi : Nat) :
 (step e prior a lo hi).2.bytes =
 if (e.buffers (e.handles a).1).val.length = lo ∨
    (e.buffers (e.handles a).1).val.length = hi
 then .Ok (e.buffers (e.handles a).1)
 else .Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData := rfl
/-- Numeric extent follows from the computed length guard on the SAME bytes. -/
theorem successful_extent (e : Entry) (prior : List Nat) (a len : Nat) (bytes : Slice U8)
 (entered : (step e prior a len len).2.bytes = .Ok bytes) :
 bytes = e.buffers (e.handles a).1 ∧ bytes.val.length = len := by
 rw [owned] at entered
 split at entered
 · rename_i size
   cases entered
   exact ⟨rfl,size.elim id id⟩
 · cases entered
#print borrowed
#print owned
#print successful_extent
#print axioms borrowed
#print axioms owned
#print axioms successful_extent
end NLM_SnapshotBridge
