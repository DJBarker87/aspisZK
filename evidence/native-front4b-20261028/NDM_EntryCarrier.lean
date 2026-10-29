import NDM_EntryReference
import NDG_AccessLaws
set_option autoImplicit false
namespace NDM_EntryCarrier
attribute [local instance] Classical.propDecidable
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.S2W_D189Entry

def admitted (e : Entry) (a l1 l2 : Nat) : Prop :=
 (e.buffers (e.handles a).1).val.length=l1 ∨
 (e.buffers (e.handles a).1).val.length=l2

theorem length (e : Entry) (a l1 l2 : Nat) :
 (e.snapshot a l1 l2).length=.Ok (Slice.len (e.buffers (e.handles a).1)) := by
 simp [Entry.snapshot]

theorem bytes_success (e : Entry) (a l1 l2 : Nat) (h : admitted e a l1 l2) :
 (e.snapshot a l1 l2).bytes=.Ok (e.buffers (e.handles a).1) := by
 unfold admitted at h
 simp only [Entry.snapshot]
 rw [if_pos h]

theorem bytes_error (e : Entry) (a l1 l2 : Nat) (h : ¬ admitted e a l1 l2) :
 (e.snapshot a l1 l2).bytes=.Err .InvalidAccountData := by
 unfold admitted at h
 simp only [Entry.snapshot]
 rw [if_neg h]

theorem data_success (ops : Ops) (e : Entry) (a l1 l2 : Nat) (h : admitted e a l1 l2) :
 r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot a l1 l2) =
 ok (.Ok (alloc.vec.Vec.deref (e.buffers (e.handles a).1))) :=
 NDG_AccessLaws.data_success _ _ _ (bytes_success e a l1 l2 h)

theorem data_error (ops : Ops) (e : Entry) (a l1 l2 : Nat) (h : ¬ admitted e a l1 l2)
 (clone : ops.op35 .InvalidAccountData=ok .InvalidAccountData) :
 r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot a l1 l2)=
 ok (.Err .InvalidAccountData) :=
 NDG_AccessLaws.data_error _ _ _ (bytes_error e a l1 l2 h) clone

#print axioms length
#print axioms bytes_success
#print axioms bytes_error
#print axioms data_success
#print axioms data_error
end NDM_EntryCarrier
