import NLM_ScalarLaws
import NGL_StorageCases
set_option autoImplicit false
noncomputable section
namespace NLM_StorageFacts
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- The concrete snapshot at its source bounds establishes the complete
CLOSED data/data_len storage domain. No chosen read, byte bound, or successful
borrow is an additional root premise here. This is source/std support only. -/
theorem snapshot (e : Entry) (a : Nat) (lo hi : Usize)
 (low : NGL_StorageCases.Allowed lo) (high : NGL_StorageCases.Allowed hi) :
 NGL_StorageCases.Domain (e.snapshot a lo.val hi.val) := by
 let bytes := e.buffers (e.handles a).1
 have len : (Slice.len bytes).val=bytes.val.length := Slice.len_val bytes
 by_cases selected : bytes.val.length=lo.val ∨ bytes.val.length=hi.val
 · have bound : bytes.val.length≤58295 := by
     rcases selected with h|h
     · rw [h]; exact NGL_StorageCases.bounded lo low
     · rw [h]; exact NGL_StorageCases.bounded hi high
   refine ⟨Or.inr (Or.inr ⟨Slice.len bytes,bytes,rfl,?_,?_,?_⟩),?_⟩
   · change (if bytes.val.length=lo.val ∨ bytes.val.length=hi.val then core.result.Result.Ok bytes else .Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)=.Ok bytes
     rw [if_pos selected]
   · exact len
   · exact len.trans_le bound
   · intro n v hn hv
     have same := core.result.Result.Ok.inj hn
     change Slice.len bytes=n at same
     subst n
     rcases selected with h|h
     · change NGL_StorageCases.Allowed (Slice.len bytes)
       unfold NGL_StorageCases.Allowed at low ⊢
       simpa only [len,h] using low
     · unfold NGL_StorageCases.Allowed at high ⊢
       simpa only [len,h] using high
 · refine ⟨Or.inr (Or.inl ⟨Slice.len bytes,rfl,?_⟩),?_⟩
   · simp [Entry.snapshot,show ¬ ((e.buffers (e.handles a).1).val.length=lo.val ∨
        (e.buffers (e.handles a).1).val.length=hi.val) from selected,if_neg]
   · intro n v hn hv
     have bad : (e.snapshot a lo.val hi.val).bytes=.Err .InvalidAccountData := by
       simp [Entry.snapshot,show ¬ ((e.buffers (e.handles a).1).val.length=lo.val ∨
         (e.buffers (e.handles a).1).val.length=hi.val) from selected,if_neg]
     rw [bad] at hv
     cases hv
#print snapshot
#print axioms snapshot
end NLM_StorageFacts
