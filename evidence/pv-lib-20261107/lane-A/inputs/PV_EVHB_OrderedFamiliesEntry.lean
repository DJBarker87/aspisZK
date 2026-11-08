import PV_OWN2_NativeCarrierView
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_OrderedFamiliesEntry
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_OWN2_Codec
open PV_OWN2_RunBorrowAddress

/-- Named caller obligation under slice-1. These are the original captured
values and their installed codecs, not a requested launch result. F and the
opaque native task retain their actual source types and byte decoders. -/
structure Captures (F Task : Type) where
  site : Site
  parentStack : Pointer
  callerStack : Pointer
  n : UsizeWord
  f : F
  handles : List Task
  fWidth : Nat
  fDecode : Image fWidth → Option F
  taskWidth : Nat
  taskDecode : Image taskWidth → Option Task

/-- Entry storage witnesses selected by the OWNER pre-state. No callback,
ThreadInit, allocation reply, runtime contract or final conclusion occurs. -/
structure Places where
  run : Place
  n : Place
  f : Place
  handles : Place

/-- Original-entry obligation for the caller's slice to discharge. All four
places are owned typed storage in the SAME pre-state. The run image contains
the actual n/F addresses from the pinned operand layout; n and F read back at
those addresses. The handles image reads exactly the captured native tasks.
PV_OWN2_ClientLayout supplies the two-word capture width; no fresh box place
or selected box header is supplied by this precondition. -/
def At {F Task : Type} (s : OWNER) (c : Captures F Task) (p : Places) : Prop :=
  TypedMemory PV_OWN2_ClientLayout.layout.capture.width decodeFatPointer s
    ⟨p.run,[runWords c.site c.parentStack c.callerStack]⟩ ∧
  UsizeMemory s ⟨p.n,[c.n]⟩ ∧
  TypedMemory c.fWidth c.fDecode s ⟨p.f,[c.f]⟩ ∧
  TypedMemory c.taskWidth c.taskDecode s ⟨p.handles,c.handles⟩ ∧
  (∀ id h, receiver s p.run=some (id,h) → h.pointer=(runAddress c.site c.parentStack).val) ∧
  (∀ id h, receiver s p.n=some (id,h) → h.pointer=(runWords c.site c.parentStack c.callerStack).1.val) ∧
  (∀ id h, receiver s p.f=some (id,h) → h.pointer=(runWords c.site c.parentStack c.callerStack).2.val)

/-- Named entry precondition, universally quantified at slice use. Its
satisfiability by the actual caller's construction remains the named caller
obligation OrderedFamiliesEntryOwned; this is not an endpoint premise or T.
No assertion about this slice's post-state appears in the precondition. -/
def OrderedFamiliesEntryOwned {F Task : Type} (s : OWNER) (c : Captures F Task) : Prop :=
  ∃ p : Places, At s c p

/-- Hypotheses: exactly OrderedFamiliesEntryOwned on the OWNER pre-state.
The captured places are its witnesses; none is chosen by erased-value matching. -/
theorem entry_places {F Task : Type} (s : OWNER) (c : Captures F Task)
    (entry : OrderedFamiliesEntryOwned s c) : ∃ p, At s c p := entry

#print axioms entry_places
end PV_EVHB_OrderedFamiliesEntry
