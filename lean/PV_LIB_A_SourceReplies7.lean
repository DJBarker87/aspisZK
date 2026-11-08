import PV_LIB_A_DeferredActions
import PV_LIB_A_WeakDropBranches
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_SourceReplies7
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_CellSetBegin PV_LIB_A_CellSetThreadId

/-- Whole status/store/world/event/stack delivery, on EVERY native answer.
The four emitted copy-type cases are supplied by emitted_copy_cases. These
are local source premises, not an actual-caller history or a new row interface. -/
theorem copy_all_replies (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (fn reference value old : Data) (wait : PV_STX2_Native.Waiting Data)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) (post : Store Data) (d : Destructor) (p : Address)
    (metadata : destructor fn = some d)
    (received : receiver C c.store w reference = some (p,old))
    (replaced : writeAddress C c.store p (some value) = some post)
    (recognized : effectFree d = true) :
    (sourceBegin C values c w es stack ⟨.cellSet504,fn,wait,[reference,value]⟩ r).base =
      let q := PV_THR2_ChildBoundary.delivered C {c with store := post} wait r
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  have projected := copy_from_source C c.store post w fn reference value old d p
    metadata received replaced recognized
  unfold sourceBegin start
  rw [projected]
  exact source_done_reply C {c with store := post} es stack
    ⟨.cellSet504,fn,wait,[reference,value]⟩ r

/-- A successful last-Weak source completion clears its BoxNew source root
before applying the SAME pinned child return rule. No arbitrary Store map. -/
theorem weak_success (C : Carrier OWNER Data) (c : Config)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : SourceSite)
    (a i : Nat) (w : OWNER) (v : Data) :
    (sourceReceive C c es stack site (.deallocate ⟨a,i,[]⟩) ⟨.returned (.ok v),w,events⟩).base =
      let q := PV_THR2_ChildBoundary.delivered C
        {c with store := write c.store ⟨a,i,[]⟩ none} site.waiting ⟨.returned (.ok v),w,events⟩
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := rfl

theorem weak_failure (C : Carrier OWNER Data) (c : Config)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : SourceSite)
    (p : Address) (w : OWNER) (error : Aeneas.Std.Error) :
    (sourceReceive C c es stack site (.deallocate p) ⟨.returned (.fail error),w,events⟩).base =
      let q := PV_THR2_ChildBoundary.delivered C c site.waiting ⟨.returned (.fail error),w,events⟩
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := rfl

theorem weak_divergence (C : Carrier OWNER Data) (c : Config)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : SourceSite)
    (p : Address) (w : OWNER) :
    (sourceReceive C c es stack site (.deallocate p) ⟨.returned .div,w,events⟩).base =
      let q := PV_THR2_ChildBoundary.delivered C c site.waiting ⟨.returned .div,w,events⟩
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := rfl

theorem weak_fault (C : Carrier OWNER Data) (c : Config)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : SourceSite)
    (p : Address) (w : OWNER) (fault : Fault) :
    (sourceReceive C c es stack site (.deallocate p) ⟨.fault fault,w,events⟩).base =
      let q := PV_THR2_ChildBoundary.delivered C c site.waiting ⟨.fault fault,w,events⟩
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  cases fault <;> rfl

/-- Retain the actual adequacy gap in the NEW candidate. A perfectly defined
source replacement is insufficient when old T has a nontrivial destructor.
This is a local model result, not reachability or a fault in frozen Rust. -/
theorem nontrivial_still_unsupported (C : Carrier OWNER Data)
    (values : Values OWNER PV_RJ4IDB.NativeEvent) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (fn reference value old : Data) (wait : PV_STX2_Native.Waiting Data)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) (post : Store Data) (d : Destructor) (p : Address)
    (metadata : destructor fn = some d)
    (received : receiver C c.store w reference = some (p,old))
    (replaced : writeAddress C c.store p (some value) = some post)
    (nontrivial : effectFree d = false) :
    (sourceBegin C values c w es stack ⟨.cellSet504,fn,wait,[reference,value]⟩ r).base.current.status =
      .undefined none c.store := by
  have begun := begin_from_source C c.store post w fn reference value old d p
    metadata received replaced
  have missing : PV_THR2_LibrarySemantics_CellSetCopy504 C fn [reference,value] c.store w = none := by
    unfold PV_THR2_LibrarySemantics_CellSetCopy504
    rw [begun]
    change (if effectFree d = true then some post else none) = none
    rw [nontrivial]
    rfl
  unfold sourceBegin start
  rw [missing]
  rfl

#print axioms copy_all_replies
#print axioms weak_success
#print axioms weak_failure
#print axioms weak_divergence
#print axioms weak_fault
#print axioms nontrivial_still_unsupported
end PV_LIB_A_SourceReplies7
