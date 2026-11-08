import PV_LIB_A_ActionAdequacyGap
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ReplyAdequacyGap
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_ActionAdequacyGap

/-- Native pending is the existing pinned rule's waiting state, without a
fresh activation or fabricated successful completion. -/
theorem pending_reply (C : Carrier OWNER Data) (c : Config)
    (wait : PV_STX2_Native.Waiting Data) (post : OWNER)
    (events : List PV_RJ4IDB.NativeEvent) :
    (PV_THR2_ChildBoundary.delivered C c wait ⟨.pending,post,events⟩).status =
      .running c := rfl

/-- Actual client panic is the already pinned abort terminal. No destructor
unwind fact can replace this client-profile rule. -/
theorem panic_reply (C : Carrier OWNER Data) (c : Config)
    (wait : PV_STX2_Native.Waiting Data) (post : OWNER)
    (events : List PV_RJ4IDB.NativeEvent) :
    (PV_THR2_ChildBoundary.delivered C c wait ⟨.fault .panic,post,events⟩).status =
      .fault .abort c.store := rfl

/-- Concrete answer-boundary mismatch for aggregate504. This is a local
machine/model counterexample, not an assertion that original-entry execution
reaches the site. The missing arbitrary-T semantics must be supplied before
using `native` or `effects` as any full-answer/source adequacy result. -/
theorem pending_not_retained (C : Carrier OWNER Data)
    (values : Values OWNER PV_RJ4IDB.NativeEvent) (c : Config) (w post : OWNER)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (generics reference : Data) (fields : List (String × Data))
    (wait : PV_STX2_Native.Waiting Data) :
    (deliver C values c w es stack
      ⟨.cellBoolSet504,token 504 generics,wait,[reference,.object fields]⟩
      ⟨.pending,post,events⟩).current.status ≠
      (PV_THR2_ChildBoundary.delivered C c wait ⟨.pending,post,events⟩).status := by
  rw [aggregate_delivery_undefined, pending_reply]
  intro impossible
  cases impossible

theorem panic_not_retained (C : Carrier OWNER Data)
    (values : Values OWNER PV_RJ4IDB.NativeEvent) (c : Config) (w post : OWNER)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (generics reference : Data) (fields : List (String × Data))
    (wait : PV_STX2_Native.Waiting Data) :
    (deliver C values c w es stack
      ⟨.cellBoolSet504,token 504 generics,wait,[reference,.object fields]⟩
      ⟨.fault .panic,post,events⟩).current.status ≠
      (PV_THR2_ChildBoundary.delivered C c wait ⟨.fault .panic,post,events⟩).status := by
  rw [aggregate_delivery_undefined, panic_reply]
  intro impossible
  cases impossible

#print axioms pending_reply
#print axioms panic_reply
#print axioms pending_not_retained
#print axioms panic_not_retained
end PV_LIB_A_ReplyAdequacyGap
