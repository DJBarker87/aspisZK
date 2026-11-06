import NLM_ReadCalls
set_option autoImplicit false
noncomputable section
namespace NLM_ActualRead
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- The actual CLOSED owned getter's successful branch identifies its stored
bytes. This is not an address-implies-payload premise. -/
theorem snapshot_bytes (ops : AdapterRw.Ops) (e : Entry) (a lo hi : Nat)
 (bytes : Slice U8)
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
   (e.snapshot a lo hi)=.ok (.Ok bytes)) :
 (e.snapshot a lo hi).bytes=.Ok bytes := by
 rw [NGL_CloneDomain.data_result] at read
 by_cases selected : (e.buffers (e.handles a).1).val.length=lo ∨ (e.buffers (e.handles a).1).val.length=hi
 · simp only [Entry.snapshot,if_pos selected] at read ⊢
   cases read
   rfl
 · simp [Entry.snapshot,selected] at read
#print snapshot_bytes
#print axioms snapshot_bytes
end NLM_ActualRead
