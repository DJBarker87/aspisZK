import PV_LIB_A_ValueDestruct9
import PV_LIB_A_GenericDropMachine
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_GenericDropMachine9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_TypedDestruct

/-- Recover erased allocator only if exact type-only resolution is missing.
The actual initialized value is read at the dropped place, never supplied. -/
def resolution (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (fn : Data) (place : PV_STX2_Syntax.Place) : Option Resolution :=
  match PV_LIB_A_GenericDropBinding.resolveToken fn with
  | some d => some d
  | none => do
    let value ← read C c.store w c.frame.activation place
    PV_LIB_A_ValueDestruct9.token C fn value

def selectDrop (C : Carrier OWNER Data) (P : Data → Option PV_STX2_SliceSyntax.Program)
    (c : Config) (w : OWNER) : Option PV_LIB_A_GenericDropMachine.DropSite := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request,wait.action with
    | .drop fn _,.dropped place =>
      let d ← resolution C c w fn place
      match d with
      | .noop => pure (.noop wait)
      | .call fn =>
        let program ← P (.object [("Regular",fn)])
        let address ← locate C c.store w c.frame.activation place
        pure (.body ⟨wait,program,address⟩)
    | _,_ => none

def resolution248 (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (fn reference : Data) : Option Resolution :=
  match PV_LIB_A_DropInPlace248.resolution fn with
  | some d => some d
  | none => do
    if PV_THR2_OffPath.functionId fn = some 248 then
      let normalized ← normalize 64 fn
      let d ← PV_LIB_A_CellSetBegin.destructor normalized
      let address ← C.dereference w reference
      let value ← readAddress C c.store address
      PV_LIB_A_ValueDestruct9.resolve C d.type d.witness value
    else none

def select248 (C : Carrier OWNER Data) (c : Config) (w : OWNER) :
    Option PV_LIB_A_DropInPlace248.Site := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request with
    | .child fn _ [reference] =>
      let d ← resolution248 C c w fn reference
      pure ⟨wait,reference,d⟩
    | _ => none

def selectCell (C : Carrier OWNER Data) (P : Data → Option PV_STX2_SliceSyntax.Program)
    (c : Config) (w : OWNER) : Option PV_LIB_A_CellDestruct504.Site := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request with
    | .child fn a args =>
      if PV_THR2_OffPath.functionId fn = some 504 ∧ (P fn).isNone = true then
        let normalized ← normalize 64 fn
        let prepared ← PV_LIB_A_CellSetBegin.PV_THR2_LibrarySemantics_CellSetBegin504 C normalized args c.store w
        let d ← PV_LIB_A_ValueDestruct9.resolve C prepared.destructor.type prepared.destructor.witness prepared.old
        pure ⟨wait,a,prepared,d⟩
      else none
    | _ => none

#print axioms resolution
#print axioms resolution248
#print axioms select248
#print axioms selectCell

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
      match select248 C c w with
      | some site => match site.destructor with
        | .noop => PV_LIB_A_GenericDropMachine.noop C c w es stack site.waiting
        | .call _ =>
          ⟨⟨⟨.running (PV_LIB_A_DropInPlace248.PV_THR2_LibrarySemantics_DropInPlace248 c site),
            w,es⟩,stack⟩,none⟩
      | none => match selectCell C P c w with
        | some site => match C.aggregate PV_LIB_A_GenericDropMachine.unitTag [] with
          | none => ⟨⟨⟨.undefined none c.store,w,es⟩,stack⟩,none⟩
          | some unit => PV_LIB_A_CellDestruct504.enter c w es stack site unit
        | none => match selectDrop C P c w with
          | some (.noop wait) => PV_LIB_A_GenericDropMachine.noop C c w es stack wait
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
      select248 C c s.base.current.world = none ∧
      selectCell C P c s.base.current.world = none ∧
      selectDrop C P c s.base.current.world = none) :
    step C K P resources encode H values s =
      PV_LIB_A_DeferredActions.step C K P resources encode H values s := by
  unfold step
  cases hp : s.applied <;> try rfl
  cases hs : s.base.current.status <;> try rfl
  rename_i c
  rcases away c hs with ⟨ptr,cell,drop⟩
  simp only [ptr,cell,drop]

#print axioms selectDrop
#print axioms step
#print axioms phase
#print axioms agreement
end PV_LIB_A_GenericDropMachine9
