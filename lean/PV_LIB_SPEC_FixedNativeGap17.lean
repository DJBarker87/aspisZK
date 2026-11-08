import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_FixedNativeGap17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_Tls18Bound16 (request)

/-- The fixed historical runtime forwards the request, but does not install
its context-bound source/TLS result adapter. Check the actual original84 poll,
not a fresh local source fixture. -/
theorem fixed_answer :
    (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).native (request 10)
      PV_LIB_SPEC_Entry14.state =
      ⟨.returned (.ok .null),PV_LIB_SPEC_Entry14.state,[]⟩ := by
  change PV_THR2_OwnUniformResourceHandler.lift
    PV_LIB_SPEC_ReachedEnvironment14.environment.native
    (PV_THR2_FnOnceDispatch.request (request 10)) PV_LIB_SPEC_Entry14.state = _
  unfold request PV_LIB_SPEC_Tls18Bound16.arguments PV_LIB_SPEC_Tls18Bound16.token
  simp only [PV_LIB_SPEC_TlsNative15.reference]
  rw [PV_THR2_FnOnceDispatch.source_request]
  have selected : PV_LIB_SPEC_TlsBindings13.selected
      (.child PV_THR2_F2Call.descriptors.2 10 [PV_LIB_SPEC_TlsNative15.reference]) = true := by
    simp [PV_LIB_SPEC_TlsBindings13.selected,PV_THR2_FnOnceDispatch.request]
  simp only [PV_LIB_SPEC_TlsNative15.reference] at selected
  have other (fn : Data) (n : Nat) (id : PV_THR2_OffPath.functionId fn = some n)
      (ne : 18 ≠ n) :
      PV_THR2_F2Call.descriptors.2 ≠ fn := by
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    change (some 18 : Option Nat) = PV_THR2_OffPath.functionId fn at bad
    rw [id] at bad
    exact ne (Option.some.inj bad)
  have h268 := other PV_LIB_SPEC_RawVec14.token 268 rfl (by decide)
  have h164 := other PV_LIB_SPEC_PreludeValues14.fn164 164 rfl (by decide)
  have h165 := other PV_LIB_SPEC_PreludeValues14.fn165 165 rfl (by decide)
  have h93 := other PV_LIB_SPEC_PreludeValues14.fn93 93 rfl (by decide)
  have h295 := other PV_LIB_SPEC_StackSize14.token 295 rfl (by decide)
  have h453 := other PV_THR2_Source361HookChildren.fnTrueFull 453 rfl (by decide)
  have h454 := other PV_THR2_Source361HookChildren.fnFalseFull 454 rfl (by decide)
  simp only [PV_THR2_OwnUniformResourceHandler.lift,
    PV_LIB_SPEC_ReachedEnvironment14.environment,PV_LIB_SPEC_ReachedEnvironment14.native,
    if_neg (show ¬(PV_THR2_F2Call.descriptors.2=PV_LIB_SPEC_RawVec14.token ∨
      PV_THR2_F2Call.descriptors.2=PV_LIB_SPEC_PreludeValues14.fn164 ∨
      PV_THR2_F2Call.descriptors.2=PV_LIB_SPEC_PreludeValues14.fn165 ∨
      PV_THR2_F2Call.descriptors.2=PV_LIB_SPEC_PreludeValues14.fn93 ∨
      PV_THR2_F2Call.descriptors.2=PV_LIB_SPEC_StackSize14.token ∨
      PV_THR2_F2Call.descriptors.2=PV_THR2_Source361HookChildren.fnTrueFull ∨
      PV_THR2_F2Call.descriptors.2=PV_THR2_Source361HookChildren.fnFalseFull) from by tauto),
    PV_LIB_SPEC_PrefixEnvironment13.native,selected,if_true]
  rfl

/-- The operational adapter computes false from source0/local20 and physical
65520, on exactly that same original poll and world. -/
theorem bound_answer (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_TlsAt84.config
      (request 10) PV_LIB_SPEC_Entry14.state =
      some ⟨.returned (.ok (.boolean false)),PV_LIB_SPEC_Entry14.state,[]⟩ := by
  exact PV_LIB_SPEC_Tls18Bound16.answer stack
    PV_LIB_SPEC_ReachedEnvironment14.parameters.resources
    PV_LIB_SPEC_TlsAt84.config PV_LIB_SPEC_Entry14.state 10
    (PV_LIB_SPEC_Tls18Reached16.active _)

/-- SPEC-C14: the trigger environment is not already a full native binding
for the fixed eighteen-contract runtime. A global identity transport would
have to identify these unequal full replies at an actually reached poll.
This is a failed local transport candidate, NOT a contradiction of Witness. -/
theorem no_reply_identity (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.answer (PV_LIB_SPEC_TlsNative15.cut stack)
      PV_LIB_SPEC_ReachedEnvironment14.parameters PV_LIB_SPEC_TlsAt84.config
      (request 10) PV_LIB_SPEC_Entry14.state ≠
      some ((runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).native
        (request 10) PV_LIB_SPEC_Entry14.state) := by
  rw [bound_answer,fixed_answer]
  intro equal
  cases equal

#print axioms fixed_answer
#print axioms bound_answer
#print axioms no_reply_identity
end PV_LIB_SPEC_FixedNativeGap17
