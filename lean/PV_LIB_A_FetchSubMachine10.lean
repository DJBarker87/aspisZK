import PV_LIB_A_FetchSubReply10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_FetchSubMachine10
open scoped Classical
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_FetchSubReply10

/-- The old-value snapshot is source CONTROL data. It holds no source Store,
allocation image, callback transformer or allocator-success premise. -/
structure State where
  base : SourceState
  saved : Option Saved := none

def wrap (s : SourceState) : State := ⟨s,none⟩

/-- No fabricated result is supplied when a retained581 phase has no matching
old-value snapshot. Such a state is an explicit interpretation gap. -/
def gap (s : SourceState) : State :=
  match s.base.current.status with
  | .running c => wrap (PV_LIB_A_WeakOwnerFree9.gap c s.base.current.world
      s.base.current.events s.base.suspended)
  | _ => wrap s

/-- Run the SAME fixed source-count operation and OWNER/resource layers. A
pending reply retains the pre-subtraction value; all other replies clear it. -/
def poll (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : SourceState) (saved : Saved) : State :=
  let out := PV_LIB_A_WeakOwnerFree10.step C K P resources encode (handler H saved) values s
  ⟨out,if out.applied.isSome then some saved else none⟩

/-- Source-aware581 value delivery. Its existing source subtraction is still
performed exactly once. On retries the saved OLD value is used, not the current
source count; arbitrary T callbacks still use the unmodified source interpreter. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State) : State :=
  match s.saved with
  | some saved => match s.base.applied,s.base.base.current.status with
    | some (site,.done),.running c =>
      if site.action = .inherited (.primitive .fetchSub581) ∧
          site.waiting = saved.waiting ∧ c.frame.waiting = some saved.waiting then
        poll C K P resources encode H values s.base saved
      else gap s.base
    | _,_ => gap s.base
  | none => match s.base.applied,s.base.base.current.status with
    | none,.running c => match selected P c with
      | none => wrap (PV_LIB_A_WeakOwnerFree10.step C K P resources encode H values s.base)
      | some site =>
        match readOld (PV_LIB_A_UnwindMatch.carrier (PV_THR2_AggregateCompletion.carrier C) K)
            c s.base.base.current.world site with
        | none => gap s.base
        | some old => poll C K P resources encode H values s.base ⟨site.waiting,old⟩
    | some (site,_),_ =>
      if site.action = .inherited (.primitive .fetchSub581) then gap s.base
      else wrap (PV_LIB_A_WeakOwnerFree10.step C K P resources encode H values s.base)
    | _,_ => wrap (PV_LIB_A_WeakOwnerFree10.step C K P resources encode H values s.base)

/-- The new layer is identical to the earlier free step at every initially
unselected source state. No callback/no-write hypothesis is used. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState)
    (phase : s.applied = none)
    (away : ∀ c, s.base.current.status = .running c → selected P c = none) :
    step C K P resources encode H values (wrap s) =
      wrap (PV_LIB_A_WeakOwnerFree10.step C K P resources encode H values s) := by
  simp only [step,wrap,phase]
  cases hs : s.base.current.status <;> try rfl
  rename_i c
  simp only [away c hs]

/-- A retained phase keeps the IDENTICAL saved old count without another read.
The source operation's own phase decides when the snapshot can be released. -/
theorem retained (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : SourceState) (saved : Saved)
    (pending : (PV_LIB_A_WeakOwnerFree10.step C K P resources encode
      (handler H saved) values s).applied.isSome = true) :
    (poll C K P resources encode H values s saved).saved = some saved := by
  simp only [poll,pending,if_true]

#print axioms wrap
#print axioms gap
#print axioms poll
#print axioms step
#print axioms agreement
#print axioms retained
end PV_LIB_A_FetchSubMachine10
