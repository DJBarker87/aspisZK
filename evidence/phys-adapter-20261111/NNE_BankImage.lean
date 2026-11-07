import NNE_ByteIdentity
import NNE_Trace
import NNE_CopyFrame
set_option autoImplicit false
noncomputable section
namespace NNE_BankImage
open Aeneas Aeneas.Std AspisR1 S2W_D189Entry S2W_ReturnedCheckpoint
open Hist_Store Hist_RuntimeEntry CPP_BankState
open RSL

def Image (s : SdkState) (bank : Bank) : Prop :=
 ∀ i, (s.cells i).payload = nativeBytes (bank.cells i).data

def Metadata (before after : Bank) : Prop :=
 (∀ i, (after.cells i).owner = (before.cells i).owner) ∧ after.lamports = before.lamports

theorem loaded (bank : Bank) (layout : Layout) (n : Nat) :
 Image (NNE_Entry.state (load bank.cells layout) n) bank := fun _ => rfl

theorem ext (a b : Bank) (bytes : ∀ i, nativeBytes (a.cells i).data = nativeBytes (b.cells i).data)
 (owners : ∀ i, (a.cells i).owner = (b.cells i).owner) (coins : a.lamports = b.lamports) : a = b := by
 have cells : a.cells = b.cells := by
  funext i
  have hd := NNE_ByteIdentity.slice _ _ (bytes i)
  have ho := owners i
  cases ha : a.cells i
  cases hb : b.cells i
  simp_all
 cases a; cases b
 simp_all

theorem frame (before after : Bank) (s post : SdkState)
 (pre : Image s before) (out : Image post after) (metadata : Metadata before after)
 (payload : ∀ i, (post.cells i).payload = (s.cells i).payload) : after = before := by
 apply ext after before _ metadata.1 metadata.2
 intro i
 exact (out i).symm.trans ((payload i).trans (pre i))

theorem copy (before after : Bank) (e : Entry) (n : Nat) (post : SdkState)
 (saved : alloc.vec.Vec U8)
 (pre : Image (NNE_Entry.state e n) before) (out : Image post after)
 (metadata : Metadata before after)
 (write : ∀ i, (post.cells i).payload =
  if i = (e.handles 2).1 then nativeBytes saved else ((NNE_Entry.state e n).cells i).payload) :
 after = ⟨commit before.cells (e.handles 2).1 saved,before.lamports⟩ := by
 apply ext
 · intro i
   have hw := write i
   rw [out i] at hw
   by_cases hi : i = (e.handles 2).1
   · subst i
     simpa [commit,Hist_Store.put,alloc.vec.Vec.deref] using hw
   · simpa [commit,Hist_Store.put,hi] using hw.trans (by simp [hi,pre i])
 · intro i
   by_cases hi : i = (e.handles 2).1
   · subst i; simpa [commit,Hist_Store.put] using metadata.1 (e.handles 2).1
   · simpa [commit,Hist_Store.put,hi] using metadata.1 i
 · exact metadata.2

/-- The runtime event projection records committed writes and rollback.
This contains no model call or model acceptance predicate. -/
def Events (es : List Event) (event : S2X.AccountEvent) : Prop :=
 ((∀ i bs, Event.write i bs ∉ es) → event = .rollback) ∧
 (∀ i bs, Event.write i bs ∈ es → event = .committedWrite i (bs.map encode))

theorem no_write (es : List Event) (event : S2X.AccountEvent)
 (rep : Events es event) (free : ∀ i bs, Event.write i bs ∉ es) : event = .rollback := rep.1 free

theorem write (es : List Event) (event : S2X.AccountEvent)
 (rep : Events es event) (i : Nat) (saved : alloc.vec.Vec U8)
 (mem : Event.write i (nativeBytes saved) ∈ es) :
 event = .committedWrite i (MultiproofConeCanonical.bytesOf saved.val) := by
 rw [← vector_representation saved]
 exact rep.2 i _ mem
#print axioms loaded
#print axioms ext
#print axioms frame
#print axioms copy
#print axioms no_write
#print axioms write
end NNE_BankImage
end
