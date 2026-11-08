import PV_LIB_A_GenericDropBinding
import PV_LIB_A_DropInPlace248
import PV_LIB_A_CellDestruct504
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_GenericDropMachine
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

/-- The same unit aggregate constructor that the retained emitted bodies use.
This is a typed source value, not a byte image or a total heap initialization. -/
def unitTag : Data := .object [("Adt",.array [.object [("id",.atom "Tuple"),
  ("generics",.object [("regions",.array []),("types",.array []),
    ("const_generics",.array []),("trait_refs",.array [])])],.null,.null])]

inductive DropSite where
  | noop (waiting : PV_STX2_Native.Waiting Data)
  | body (site : PV_LIB_A_TypedDropSource.Site)

/-- All typed source-resolved Drop bodies, not just608. Trait dispatch retains
the actual self type. Unresolved/opaque glue is explicitly outside this selector. -/
def selectDrop (C : Carrier OWNER Data) (P : Data → Option PV_STX2_SliceSyntax.Program)
    (c : Config) (w : OWNER) : Option DropSite := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request,wait.action with
    | .drop fn _,.dropped place =>
      let d ← PV_LIB_A_GenericDropBinding.resolveToken fn
      match d with
      | .noop => pure (.noop wait)
      | .call fn =>
        let program ← P (.object [("Regular",fn)])
        let address ← locate C c.store w c.frame.activation place
        pure (.body ⟨wait,program,address⟩)
    | _,_ => none

/-- Successful no-op destruction still invalidates the dropped operand through
the ordinary delivery action. Source/parser gaps remain undefined. -/
def noop (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (wait : PV_STX2_Native.Waiting Data) : SourceState :=
  match C.aggregate unitTag [] with
  | none => ⟨⟨⟨.undefined none c.store,w,es⟩,stack⟩,none⟩
  | some unit =>
    let q := PV_THR2_ChildBoundary.delivered C c wait ⟨.returned (.ok unit),w,[]⟩
    ⟨⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩,none⟩

/-- Source layers operate only before a retained native phase. Source-resolved
calls then execute on the same OWNER base, source store, resources, handler and
full cleanup syntax. There is no final-store parameter or success premise. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState) : SourceState :=
  match s.applied with
  | some _ => PV_LIB_A_DeferredActions.step C K P resources encode H values s
  | none => match s.base.current.status with
    | .running c =>
      let w := s.base.current.world
      let es := s.base.current.events
      let stack := s.base.suspended
      match PV_LIB_A_DropInPlace248.select c with
      | some site => match site.destructor with
        | .noop => noop C c w es stack site.waiting
        | .call _ =>
          ⟨⟨⟨.running (PV_LIB_A_DropInPlace248.PV_THR2_LibrarySemantics_DropInPlace248 c site),
            w,es⟩,stack⟩,none⟩
      | none => match PV_LIB_A_CellDestruct504.select C P c w with
        | some site => match C.aggregate unitTag [] with
          | none => ⟨⟨⟨.undefined none c.store,w,es⟩,stack⟩,none⟩
          | some unit => PV_LIB_A_CellDestruct504.enter c w es stack site unit
        | none => match selectDrop C P c w with
          | some (.noop wait) => noop C c w es stack wait
          | some (.body site) => PV_LIB_A_TypedDropSource.enter C c w es stack site
          | none => PV_LIB_A_DeferredActions.step C K P resources encode H values s
    | _ => PV_LIB_A_DeferredActions.step C K P resources encode H values s

theorem phase (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (applied : SourceSite × Tail) :
    step C K P resources encode H values ⟨s,some applied⟩ =
      PV_LIB_A_DeferredActions.step C K P resources encode H values ⟨s,some applied⟩ := rfl

/-- One local agreement with the inherited staged machine at unselected states.
Its earlier OWNER agreement and resource channel are retained, not replaced. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState)
    (away : ∀ c, s.base.current.status = .running c →
      PV_LIB_A_DropInPlace248.select c = none ∧
      PV_LIB_A_CellDestruct504.select C P c s.base.current.world = none ∧
      selectDrop C P c s.base.current.world = none) :
    step C K P resources encode H values s =
      PV_LIB_A_DeferredActions.step C K P resources encode H values s := by
  unfold step
  cases hp : s.applied <;> try rfl
  cases hs : s.base.current.status <;> try rfl
  rename_i c
  rcases away c hs with ⟨ptr,cell,drop⟩
  simp only [ptr,cell,drop]

#print axioms unitTag
#print axioms selectDrop
#print axioms noop
#print axioms step
#print axioms phase
#print axioms agreement
end PV_LIB_A_GenericDropMachine
