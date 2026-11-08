import PV_LIB_A_ActiveSetter17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveFrames17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_A_ActiveDispatch17

theorem fn18_distinct : PV_THR2_F2Call.descriptors.2 ≠ PV_LIB_A_F5FullEntry16.closure := by
  intro eq
  have shape := congrArg PV_THR2_FnOnceDispatch.isFnDef eq
  change true = false at shape
  cases shape

theorem fn18_unchanged (a : Nat) (tuple : Data) :
    resolve (.child PV_THR2_RunTlsCallable.descriptors.1 a
      [PV_THR2_F2Call.descriptors.2,tuple]) = none := by
  simp only [resolve,eq_self,true_and,fn18_distinct,if_false]

/-- The existing f2 forwarding shim is consumed by name, separately. -/
theorem fn18_forwarded (a : Nat) (pointer : Address) :
    PV_THR2_FnOnceDispatch.request (.child PV_THR2_RunTlsCallable.descriptors.1 a
      [PV_THR2_F2Call.descriptors.2,
       PV_THR2_KeyValues.pack PV_THR2_RunTlsCallable.descriptors.2
        [PV_STX2_TypedReferences.reference pointer .null]]) =
      .child PV_THR2_F2Call.descriptors.2 a [PV_STX2_TypedReferences.reference pointer .null] :=
  PV_THR2_FnOnceDispatch.source_request a pointer

/-- After statement, complete reply, without selecting successful/pending
branches. The actual replacement argument comes from f207.args by name. -/
theorem after (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (a : Nat) (pointer : Address) (w : OWNER) :
    answer cut p c (PV_LIB_A_F5ClosurePending16.request a pointer) w =
      PV_LIB_SPEC_ReachedNative14.answer cut p c (setter a pointer) w := by
  simp only [answer,actual]

/-- Source and native channels are composed before the original child return
administration. ALL native reply branches, worlds and event lists are retained. -/
theorem full (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (wait : PV_STX2_Native.Waiting Data) (a : Nat) (pointer : Address)
    (w : OWNER) (r : Reply OWNER Event Data) (t : Store Data)
    (request : wait.request = PV_LIB_A_F5ClosurePending16.request a pointer)
    (native : PV_LIB_SPEC_ReachedNative14.answer cut p c (setter a pointer) w = some r)
    (source : PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_CellReplace289
      (runtime p).carrier (PV_FN_THREAD_f207.args pointer) c.store w = some t) :
    boundary cut p c wait w =
      some (PV_THR2_ChildBoundary.delivered (runtime p).carrier {c with store := t} wait r) := by
  unfold boundary
  rw [request,actual]
  change (do
    let reply ← PV_LIB_SPEC_ReachedNative14.answer cut p c (setter a pointer) w
    let store ← PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_CellReplace289
      (runtime p).carrier (PV_FN_THREAD_f207.args pointer) c.store w
    pure (PV_THR2_ChildBoundary.delivered (runtime p).carrier {c with store := store} wait reply)) = _
  rw [native]
  change (do
    let store ← PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_CellReplace289
      (runtime p).carrier (PV_FN_THREAD_f207.args pointer) c.store w
    pure (PV_THR2_ChildBoundary.delivered (runtime p).carrier {c with store := store} wait r)) = _
  rw [source]
  rfl

theorem source_frame (s : Store Data) (q : Address) (other : q ≠ PV_LIB_SPEC_Entry13.slot.source) :
    (write s PV_LIB_SPEC_Entry13.slot.source (some (.boolean true))).cells q = s.cells q :=
  write_other _ _ _ _ other

theorem physical_frame (w : OWNER) (q : Nat) (other : q ≠ PV_LIB_SPEC_Entry13.slot.physical) :
    (PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot w true).world.memory q = w.world.memory q :=
  PV_LIB_SPEC_CellPhysical13.away _ _ _ _ other

#print axioms fn18_distinct
#print axioms fn18_unchanged
#print axioms fn18_forwarded
#print axioms after
#print axioms full
#print axioms source_frame
#print axioms physical_frame
end PV_LIB_A_ActiveFrames17
