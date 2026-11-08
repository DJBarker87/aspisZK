import PV_FN_THREAD_f213Frame
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361NameEntryValidity
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_FN_THREAD_f361 PV_THR2_LibrarySemantics_ThreadNew213

/-- Exactly the additional caller-supplied name ownership/validity clause.
No later read, call, successful answer or Scope separation is in this clause.
The opaque String interpretation is explicit, not a claimed binary theorem. -/
def EntryName (R : Representation) (x : Input) : Prop :=
  ∃ view, NameOwned R x.w x.threadName view ∧
    ∀ b, view = some b → b.pointer < 2^64

/-- Thread10/slice11 entry refinement; the old Pre is retained unchanged. -/
def Pre' (R : Representation) (x : Input) : Prop := Pre x ∧ EntryName R x

theorem implies_old (R : Representation) (x : Input) (pre : Pre' R x) : Pre x := pre.1

/-- The original call-entry OWNER invariant supplies the buffer's age from
its actual registration, not from an extra alias/freshness premise. -/
theorem buffer_older (R : Representation) (x : Input) (pre : Pre x)
    (value : Data) (b : Buffer) (owned : Owned x.w b) : b.address.activation < x.a := by
  obtain ⟨id,h,registered,_⟩ := owned
  exact pre.owner.owner.activations (sourcePlace b.address) id registered

theorem owned_some (R : Representation) (w : OWNER) (label : Data) (view : Option Buffer)
    (owned : NameOwned R w label view) (b : Buffer) (selected : view = some b) : Owned w b := by
  cases owned with
  | none descriptor metadata => cases selected
  | some descriptor metadata value buffer decoded valid =>
    cases selected
    exact valid

theorem outside_scope (R : Representation) (x : Input) (pre : Pre x)
    (view : Option Buffer) (owned : NameOwned R x.w x.threadName view) :
    ¬ InBuffer view ⟨x.a,4,[]⟩ := by
  rintro ⟨b,viewEq,root⟩
  have older := buffer_older R x pre x.threadName b (owned_some R x.w x.threadName view owned b viewEq)
  have activation := congrArg Address.activation root
  change x.a = b.address.activation at activation
  omega

/-- The existing lift changes backend state only. Heap bytes, headers,
allocation metadata, live flags and the ghost registry are definitional
frames. This introduces no new handler restriction. -/
theorem owned_withWorld (w : OWNER) (backend : PV_STX_World.World) (b : Buffer)
    (owned : Owned w b) : Owned (withWorld w backend) b := by
  exact owned

theorem name_withWorld (R : Representation) (w : OWNER)
    (backend : PV_STX_World.World) (label : Data) (view : Option Buffer)
    (owned : NameOwned R w label view) : NameOwned R (withWorld w backend) label view := by
  cases owned with
  | none descriptor metadata => exact .none descriptor metadata
  | some descriptor metadata value buffer decoded valid =>
    exact .some descriptor metadata value buffer decoded (owned_withWorld w backend buffer valid)

theorem name_lift {E : Type} (R : Representation) (H : PV_W1_OwnerNativeFrame.Backend E)
    (request : PV_STX2_Native.Request Data) (w : OWNER) (label : Data) (view : Option Buffer)
    (owned : NameOwned R w label view) :
    NameOwned R (PV_THR2_OwnUniformResourceHandler.lift H request w).world label view :=
  name_withWorld R w (H request (world w)).world label view owned

#print axioms EntryName
#print axioms Pre'
#print axioms implies_old
#print axioms buffer_older
#print axioms owned_some
#print axioms outside_scope
#print axioms owned_withWorld
#print axioms name_withWorld
#print axioms name_lift
end PV_FN_THREAD_f361NameEntryValidity
