import R1Z.PV_OWND_ActualInitialized
import R1Z.PV_OWND_InitialNormal
import R1Z.PV_OWND_InitialAbort
import R1Z.PV_OWND_InitialDrop
import R1Z.PV_OWND_CheckSource
set_option autoImplicit false
attribute [local irreducible] R1Z.PV_OWND_ActualBytes.initialized
namespace R1Z.PV_OWND_FocusedReplay
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWN_Bytes
/-- Focused allocation/stores replay only. It does not assert the native
endpoint-check or complete collector law, which remain outside this root. -/
theorem constructed {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (w : State S X)
 (owner p : Nat) (s : S) (payload : Nat → Link → Bytes)
 (ctx:PV_OWND_InitialContext.Context prim w owner)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s))
 (agrees:∀ i v, PV_OWNB_Padding.Agrees (PV_OWNB_LinkBytes.encode v) (payload i v))
 (oom : Action S X E (Buffer Link)) :
 let r:=PV_OWND_InitialRun.construct prim owner oom payload w
 ∃ b, r.outcome=.ok b ∧ PV_OWNC_Vector.Valid PV_OWNB_LinkCodec.codec b ∧
 b.length=127 ∧ b.capacity=127 ∧ r.world.memory=b.memory ∧ r.world.allocator=s ∧
 r.world.extra=w.extra ∧ r.calls=[(w,.allocate 1016 2)] := by
 dsimp only
 rw [PV_OWND_InitialSuccess.complete prim owner p oom payload w s h]
 have hb:=PV_OWND_ActualInitialized.constructed prim w owner p s payload ctx h agrees
 refine ⟨_,rfl,hb.1,hb.2.1,hb.2.2.1,rfl,?_,rfl,rfl⟩
 simp only [allocate,emit,h]
#print axioms constructed
end R1Z.PV_OWND_FocusedReplay
