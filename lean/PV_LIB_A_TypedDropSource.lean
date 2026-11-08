import PV_LIB_A_DeferredActions
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_TypedDropSource
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

/-- Emitted Drop uses an FnPtr; ordinary calls wrap the SAME FnPtr in Regular.
Preserve every generic/type/trait item rather than resolving by a numeric id. -/
def callToken : Data → Data
  | .object [("Regular",fn)] => .object [("Regular",fn)]
  | fn => .object [("Regular",fn)]

structure Site where
  waiting : PV_STX2_Native.Waiting Data
  program : PV_STX2_SliceSyntax.Program
  address : Address

/-- Expand a source-resolved destructor at its retained typed Drop boundary.
Only the known SIZED SpawnHooks glue608 is selected. Other destructors
remain in the inherited handler with NO source
adequacy claim. This machinery alone does not bind generic UntrackedDestruct. -/
def select (C : Carrier OWNER Data) (P : Data → Option PV_STX2_SliceSyntax.Program)
    (c : Config) (w : OWNER) : Option Site := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request,wait.action with
    | .drop fn _,.dropped place =>
      if PV_THR2_OffPath.functionId (callToken fn) = some 608 then
        let program ← P (callToken fn)
        let address ← locate C c.store w c.frame.activation place
        pure ⟨wait,program,address⟩
      else none
    | _,_ => none

/-- Drop glue's emitted argument is &mut T. Its body shares the actual source
store and saves the original dropping frame, whose .dropped return action will
invalidate the operand only after completion. No final Store or callback delta
is supplied. This entry is for source-resolved sized drop glue (e.g.608).
Unsized metadata/opaque bindings and source adequacy remain separate. -/
def enter (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : Site) : SourceState :=
  let a := c.store.nextActivation
  let store := PV_STX2_Native.arguments a [C.reference site.address .null] 1
    {c.store with nextActivation := a+1}
  ⟨⟨⟨.running ⟨{activation := a,remaining := site.program.body},c.frame :: c.callers,store⟩,w,es⟩,stack⟩,none⟩

/-- A NEW typed-dispatch layer. Native replies inside the destructor are handled
by the same staged OWNER/source machine, including its failure/pending paths.
There is no whole-function H reply substituted for the resolved source body. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState) : SourceState :=
  match s.applied with
  | some _ => PV_LIB_A_DeferredActions.step C K P resources encode H values s
  | none => match s.base.current.status with
    | .running c => match select C P c s.base.current.world with
      | some site => enter C c s.base.current.world s.base.current.events s.base.suspended site
      | none => PV_LIB_A_DeferredActions.step C K P resources encode H values s
    | _ => PV_LIB_A_DeferredActions.step C K P resources encode H values s

theorem resolved (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : Site) (selected : select C P c w = some site) :
    step C K P resources encode H values ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩ =
      enter C c w es stack site := by
  simp only [step,selected]

/-- Local dispatch agreement on every state which does not resolve a Drop body.
The deferred/native layer, with its identical resource channel, is retained. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState)
    (away : ∀ c, s.base.current.status = .running c → select C P c s.base.current.world = none) :
    step C K P resources encode H values s =
      PV_LIB_A_DeferredActions.step C K P resources encode H values s := by
  unfold step
  cases phase : s.applied <;> try rfl
  cases hs : s.base.current.status <;> try rfl
  rename_i c
  simp only [away c hs]

/-- One fresh source activation, exact parent frame, world/events and intrinsic
stack. This is a local counter transition, not counter equality across a row. -/
theorem entry_frame (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : Site) :
    ∃ next, (enter C c w es stack site).base.current.status = .running next ∧
      next.frame.activation = c.store.nextActivation ∧
      next.callers = c.frame :: c.callers ∧
      next.store.nextActivation = c.store.nextActivation+1 ∧
      (enter C c w es stack site).base.current.world = w ∧
      (enter C c w es stack site).base.current.events = es ∧
      (enter C c w es stack site).base.suspended = stack :=
  ⟨_,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms callToken
#print axioms select
#print axioms enter
#print axioms step
#print axioms resolved
#print axioms agreement
#print axioms entry_frame
end PV_LIB_A_TypedDropSource
