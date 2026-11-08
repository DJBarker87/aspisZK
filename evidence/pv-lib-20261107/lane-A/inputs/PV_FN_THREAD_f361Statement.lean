import PV_FN_THREAD_f361Provider124Counts
import PV_FN_THREAD_f361Calls126
import PV_FN_THREAD_f361Bridged443
import PV_THR2_OwnInitActualAllocationOwnedBridged
import PV_THR2_OwnInitBridgeTypedRepresentation
import PV_THR2_OrderedFamiliesEntryRefined
import PV_THR2_TypedRepresentation_Thread
import PV_FN_THREAD_f361PostInitComposition
import PV_FN_THREAD_f361ErrorComposition
set_option autoImplicit false
noncomputable section

namespace PV_FN_THREAD_f361
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_OWN2_Codec
open scoped Classical

abbrev State := PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent
abbrev Backend := PV_W1_OwnerNativeFrame.Backend PV_RJ4IDB.NativeEvent

/-- Own call-entry data. Neither a future configuration nor a successful
callee answer is input. `changes` records arbitrary native source-memory
effects; it is not replaced by the zero delta in the earlier source helpers. -/
structure Input where
  C : Carrier OWNER Data
  b : Bool
  K : Control
  P : Data → Option PV_STX2_SliceSyntax.Program
  native : Backend
  /-- Frozen source/binary projection for the named thread21 adequacy
  obligation. Its correspondence is still open; choosing a model function
  here does not discharge that source/binary obligation. -/
  sourceStep : State → State
  changes : PV_W1_LeafBoundary.Entry → OWNER → Address → Option Data
  resources : Resources
  encode : Encode
  granted : PV_OWN2_FreshAllocation.GrantedRegions
  arcShape : PV_THR2_TypedRepresentation_ArcInner.Shape
  loadBias : Pointer
  siteIndex : Fin 11
  s : Store Data
  a : Nat
  dest : Nat
  parent : Frame
  parents : List Frame
  wait : PV_STX2_Native.Waiting Data
  threadName : Data
  stackSize : Data
  noHooks : Data
  scope : Data
  captured : Data
  w : OWNER
  es : List PV_RJ4IDB.NativeEvent
  stack : List Config

def base (x : Input) : Carrier OWNER Data :=
  PV_THR2_OwnInitExactReturnedCases.carrier
    (PV_THR2_OperatorSemantics_14121.carrier
      (PV_THR2_OperatorSemantics_14119.carrier
        (PV_THR2_BoxDynBinaryLayout.symbols x.loadBias x.siteIndex) x.C)) x.b

def handler (x : Input) := PV_THR2_OwnUniformResourceHandler.lift x.native

def entry (x : Input) : State :=
  ⟨⟨.running ⟨{activation := x.a,remaining := PV_THR2_F361.live.body},
    x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩

/-- Only entry validity and ownership. In particular no clone Valid,
read13726, callback address, decoder success, or ready-at14756 clause. -/
structure Pre (x : Input) : Prop where
  owner : PV_FN_THREAD_OwnerWellFormed.CallEntryOwner x.w x.s x.a
  arguments : ∀ i v, (i,v) ∈
    [(1,x.threadName),(2,x.stackSize),(3,x.noHooks),(4,x.scope),(5,x.captured)] →
      x.s.cells ⟨x.a,i,[]⟩ = some v
  saved : x.parent.waiting = some x.wait
  action : x.wait.action = .child x.a (.local x.dest)
  callers : ∀ f ∈ x.parent :: x.parents, f.activation < x.a
  suspended : ∀ c ∈ x.stack, ∀ f ∈ c.frame :: c.callers, f.activation < x.a
  captureOwned : ∃ (F Task : Type) (captures : PV_EVHB_OrderedFamiliesEntry.Captures F Task),
    PV_THR2_OrderedFamiliesEntryRefined.OrderedFamiliesEntryOwned' x.w captures x.captured
  scopeOwned : ∀ v, (base x).field x.scope 0 = some v →
    ∃ p : Address, v = PV_FN_THREAD_f222_EntryOwned.root p ∧ p.activation < x.a

/-- The provider input is constructed from the actual operand-issued store,
not from the f361 entry store or the retired consumer representation. -/
def input124 (x : Input) (e : PV_W1_LeafBoundary.Entry) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) : PV_FN_THREAD_f361Provider124.Input :=
  let c := PV_THR2_IntrinsicFrameEnter.entered e.store e.caller e.parents e.loops
    e.rest e.callee e.arguments e.destination PV_THR2_F124.live
  {C := PV_THR2_OperatorSemantics_14121.carrier
      (PV_THR2_OperatorSemantics_14119.carrier
        (PV_THR2_BoxDynBinaryLayout.symbols x.loadBias x.siteIndex) x.C),
   b := x.b,K := x.K,P := x.P,H := handler x,
   s := c.store,a := c.frame.activation,dest := e.destination,
   parent := (PV_W1_LeafBoundary.pending e).frame,parents := e.parents,
   wait := PV_THR2_StaticReply.wait e.store e.callee e.arguments e.destination,
   ptr := e.arguments.headD .null,allocator := PV_THR2_Packet218ReturnData.allocator,
   w := w,es := es,stack := e.suspended}

/-- A call cut includes the actual move-invalidated store. This is a
specification predicate, not a second source interpreter. -/
def AtCall (x : Input) (q : State) (e : PV_W1_LeafBoundary.Entry) : Prop :=
  ∃ c site args cleanup,
    q.current.status = .running c ∧ c.frame.activation = x.a ∧
    c.frame.waiting = none ∧ c.frame.unwinding = none ∧
    c.frame.remaining = .leaf (.call site e.callee args (.local e.destination) cleanup) :: e.rest ∧
    operands (base x) q.current.world x.a args c.store = some (e.arguments,e.store) ∧
    e.caller = x.a ∧ e.parents = c.callers ∧ e.loops = c.frame.loops ∧
    e.suspended = q.suspended

/-- Every stopped boundary retains its complete state. A successful summary
restores precisely the saved caller continuation. -/
def SummaryEnd (e : PV_W1_LeafBoundary.Entry) (q : State) : Prop :=
  PV_FN_THREAD_NonreturnFrontier.Frozen q ∨
  ∃ s, q.current.status = .running
    ⟨{activation := e.caller,remaining := e.rest,loops := e.loops},e.parents,s⟩

/-- The provider's own all-answer case tree selects the summary output.
An arbitrary intermediate waiting state is not a pending ANSWER. -/
def outcome124 (x : Input) (y : PV_FN_THREAD_f361Provider124.Input) : State :=
  match (PV_FN_THREAD_f124_BoxContract.strong y x.native).answer with
  | .returned (.ok sv) =>
    match (PV_FN_THREAD_f124_BoxContract.weak y x.native).answer with
    | .returned (.ok wv) =>
      let allocation := PV_FN_THREAD_f124_Interface.allocationOut y x.native
        x.resources x.encode x.arcShape sv wv
      match (x.resources (.malloc x.arcShape.layout.width)
          (world (PV_FN_THREAD_f124_BoxContract.weak y x.native).world)).answer with
      | .returned (.ok heap) => if heap = 0 then allocation else
        let z := PV_FN_THREAD_f124_ClosedLeak.input y x.native x.resources x.encode x.arcShape sv wv
        let afterRaw := PV_FN_THREAD_f124_LeakFailure.finish y
          (PV_FN_THREAD_f216.firstOut z x.native)
          (PV_FN_THREAD_f216_ReturnedStage.rawReply (PV_FN_THREAD_f216.installed z x.native))
        let afterForget := PV_FN_THREAD_f124_LeakFailure.finish y
          (PV_FN_THREAD_f216.secondOut z x.native
            (PV_FN_THREAD_f124_StorePost.backing y sv wv))
          (PV_FN_THREAD_f216_ReturnedStage.forgetReply (PV_FN_THREAD_f216.installed z x.native)
            PV_THR2_Packet216Children.fn5 PV_THR2_Packet218ReturnData.allocator
            (PV_FN_THREAD_f124_StorePost.backing y sv wv))
        match (PV_FN_THREAD_f216.baseRaw z x.native).answer with
        | .returned (.ok _) =>
          match (PV_FN_THREAD_f216.baseForget z x.native).answer with
          | .returned (.ok _) =>
            match ((handler x) (.child PV_THR2_Packet124ReturnData.intoFn
              (y.s.nextActivation+6)
              [PV_STX2_TypedReferences.reference
                (PV_FN_THREAD_f124_StorePost.backing y sv wv) .null]) z.w).answer with
            | .returned (.ok _) =>
              PV_FN_THREAD_f124.successOut y x.native x.resources x.encode x.arcShape sv wv
            | _ => PV_FN_THREAD_f124_IntoReached.outcome y x.native x.resources x.encode x.arcShape sv wv
          | _ => afterForget
        | _ => afterRaw
      | _ => allocation
    | _ => PV_FN_THREAD_f124_Interface.secondOut y x.native sv
  | _ => PV_FN_THREAD_f124_Interface.firstOut y x.native

def outcome126 (x : Input) (y : PV_FN_THREAD_f126_ReturnedStage.Input PV_RJ4IDB.NativeEvent)
    (arc p : Address) : State :=
  match (PV_FN_THREAD_f222.baseReply
      (PV_FN_THREAD_f126_ReturnedStage.childInput y arc) x.native).answer with
  | .returned (.ok _) => PV_FN_THREAD_f126.successOut y arc p
  | _ => PV_FN_THREAD_f126_Other.after y x.native arc

/-- D877 BODY summary evidence. The actual provider Post and operational
result occur together, on their complete stores. No BODY is a native reply. -/
def Body124 (x : Input) (e : PV_W1_LeafBoundary.Entry) (q out : State) : Prop :=
  let y := input124 x e q.current.world q.current.events
  PV_THR2_OffPath.functionId e.callee = some 124 ∧
  PV_FN_THREAD_f124.Pre y ∧
  PV_FN_THREAD_f124.Post y x.native x.resources x.encode x.arcShape ∧
  out = outcome124 x y ∧
  PV_FN_THREAD_f124.Reached y x.native x.resources x.encode x.arcShape out ∧
  SummaryEnd e out

def Body126 (x : Input) (e : PV_W1_LeafBoundary.Entry) (q out : State) : Prop :=
  ∃ (y : PV_FN_THREAD_f126_ReturnedStage.Input PV_RJ4IDB.NativeEvent) (arc p : Address),
    PV_THR2_OffPath.functionId e.callee = some 126 ∧
    y.C = (input124 x e q.current.world q.current.events).C ∧ y.b = x.b ∧
    y.K = x.K ∧ y.P = x.P ∧
    PV_FN_THREAD_f126_Arbitrary.entry y =
      ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.entered e.store e.caller e.parents e.loops
        e.rest e.callee e.arguments e.destination PV_THR2_F126.live),q.current.world,
        q.current.events⟩,q.suspended⟩ ∧
    PV_FN_THREAD_f126.Pre y arc p ∧ PV_FN_THREAD_f126.Post y x.native arc p ∧
    out = outcome126 x y arc p ∧
    PV_FN_THREAD_f126.Reached y x.native arc out ∧ SummaryEnd e out

def Body443 (x : Input) (e : PV_W1_LeafBoundary.Entry) (q out : State) : Prop :=
  ∃ y : PV_FN_THREAD_f443.Input PV_RJ4IDB.NativeEvent,
    PV_THR2_OffPath.functionId e.callee = some 443 ∧
    y.C = (input124 x e q.current.world q.current.events).C ∧ y.b = x.b ∧
    y.K = x.K ∧ y.P = x.P ∧ y.native = x.native ∧
    PV_FN_THREAD_f443Entry13.entry y =
      ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.entered e.store e.caller e.parents e.loops
        e.rest e.callee e.arguments e.destination PV_THR2_F443.live),q.current.world,
        q.current.events⟩,q.suspended⟩ ∧
    PV_FN_THREAD_f443.Pre y ∧ PV_FN_THREAD_f443.Post y ∧
    (if PV_FN_THREAD_f443Entry13.Returned134 y then
      if PV_FN_THREAD_f443Entry13.Returned344 y then
        ∃ d, (PV_FN_THREAD_f443Entry13.q13 y).current.status = .running d ∧
          out = ⟨⟨.running ⟨{y.parent with waiting := none},y.parents,
            PV_FN_THREAD_f443.final y d⟩,(PV_FN_THREAD_f443Entry13.q13 y).current.world,
            (PV_FN_THREAD_f443Entry13.q13 y).current.events⟩,y.stack⟩
      else out = PV_FN_THREAD_f443Entry13.q13 y
    else out = PV_FN_THREAD_f443Entry13.q6 y) ∧
    PV_FN_THREAD_f443.Reaches y out ∧ SummaryEnd e out

def Body458 (x : Input) (e : PV_W1_LeafBoundary.Entry) (q out : State) : Prop :=
  ∃ y : PV_FN_THREAD_f458Entry.Input PV_RJ4IDB.NativeEvent,
    PV_THR2_OffPath.functionId e.callee = some 458 ∧
    y.C = (input124 x e q.current.world q.current.events).C ∧ y.b = x.b ∧
    y.K = x.K ∧ y.P = x.P ∧ y.native = x.native ∧
    PV_FN_THREAD_f458Entry.entry y =
      ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.entered e.store e.caller e.parents e.loops
        e.rest e.callee e.arguments e.destination PV_THR2_F458.live),q.current.world,
        q.current.events⟩,q.suspended⟩ ∧
    PV_FN_THREAD_f458Entry.Pre y ∧ PV_FN_THREAD_f458.PostWithPointer y ∧
    (match (PV_FN_THREAD_f537.reply (PV_FN_THREAD_f458Entry.child y)).answer with
    | .returned (.ok unique) =>
      let r := PV_FN_THREAD_f537.reply (PV_FN_THREAD_f458Entry.child y)
      out = ⟨⟨.running ⟨{y.parent with waiting := none},y.parents,
        PV_FN_THREAD_f458Success.final y unique⟩,r.world,y.es ++ r.events⟩,y.stack⟩
    | _ =>
      let c := PV_FN_THREAD_f458Entry.child y
      out = PV_FN_THREAD_f537Boundary.delivered (PV_FN_THREAD_f537.base c) c.s c.a
        (c.parent :: c.parents) c.raw (PV_FN_THREAD_f537.reply c) c.es c.stack) ∧
    (∃ n, PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f458Entry.base y) y.K
      (PV_FN_THREAD_f537Run.programs y.P) (PV_FN_THREAD_f458Entry.handler y) n
      (PV_FN_THREAD_f458Entry.entry y) = out) ∧ SummaryEnd e out

/-- No ordinary source edge may consume a successful call operand. Its
full store must instead appear in one of the summary rules below. -/
def SourceOnly (x : Input) (q : State) : Prop :=
  ∀ c, q.current.status = .running c →
    c.frame.activation = x.a ∧ c.frame.waiting = none ∧
    (∀ site fn args dest cleanup rest,
      c.frame.remaining = .leaf (.call site fn args dest cleanup) :: rest →
      operands (base x) q.current.world c.frame.activation args c.store = none) ∧
    (∀ site slot fn conditional cleanup rest,
      c.frame.remaining = .leaf (.drop site (.local slot) fn conditional cleanup) :: rest →
      c.store.cells ⟨x.a,slot,[]⟩ = none)

def callbackFn : Data := PV_W1_NamedLeafBoundary.function PV_THR2_F361.node125

def nativeReply (x : Input) (q : State) (e : PV_W1_LeafBoundary.Entry) :=
  match q.current.status with
  | .running c =>
    if PV_THR2_OperatorAction.selected c = some PV_THR2_OperatorAction.Kind.clone214 then
      PV_THR2_OperatorCloneHandler.handler (base x) c (handler x)
        (.child e.callee e.store.nextActivation e.arguments) q.current.world
    else (handler x) (.child e.callee e.store.nextActivation e.arguments) q.current.world
  | _ => (handler x) (.child e.callee e.store.nextActivation e.arguments) q.current.world

/-- Finite proof certificate for caller instructions and full-state summaries.
This relation specifies the D877 composition to prove; it does not modify any
retained interpreter. Native effects use W1's exact finalStore definition. -/
inductive Run (x : Input) : State → State → Type where
  | refl (q) : Run x q q
  | source (q r out)
      (sourceOnly : SourceOnly x q)
      (step : PV_THR2_OwnInitInterpreterBridged.step (base x) x.K
        (fun _ => none) x.resources x.encode (handler x) q = r)
      (tail : Run x r out) : Run x q out
  | native (q r out e)
      (call : AtCall x q e)
      (leaf : PV_THR2_OffPath.functionId e.callee ∉ [some 124,some 126,some 443,some 458])
      (notCallback : e.callee ≠ callbackFn)
      (notInit : e.callee ≠ PV_THR2_Source361InitChildren.fnAllocationFull)
      (post : PV_W1_LeafBoundary.Post
        (PV_W1_ArgumentEffects.afterEffects (base x) e q.current.world
          (x.changes e q.current.world)) (nativeReply x q e) q.current.events r)
      (result : r = PV_W1_LeafBoundary.deliver (base x)
        (PV_W1_ArgumentEffects.afterEffects (base x) e q.current.world
          (x.changes e q.current.world))
        (nativeReply x q e)
        q.current.events)
      (tail : Run x r out) : Run x q out
  | callback (q r out e)
      (call : AtCall x q e) (function : e.callee = callbackFn)
      (result : r = PV_W1_LeafBoundary.deliver (base x) e
        (PV_THR2_ClosureBoxAllocation.reply x.resources x.encode e.store q.current.world)
        q.current.events)
      (tail : Run x r out) : Run x q out
  | initAllocation (q r out e)
      (call : AtCall x q e)
      (function : e.callee = PV_THR2_Source361InitChildren.fnAllocationFull)
      (result : r = PV_W1_LeafBoundary.deliver (base x) e
        (PV_THR2_OwnInitAllocationHandlerBridged.handler x.resources x.encode (handler x)
          (.child e.callee e.store.nextActivation e.arguments) q.current.world)
        q.current.events)
      (tail : Run x r out) : Run x q out
  | body (q r out e)
      (call : AtCall x q e)
      (summary : Body124 x e q r ∨ Body126 x e q r ∨ Body443 x e q r ∨ Body458 x e q r)
      (tail : Run x r out) : Run x q out
  | drop (q r out c site slot fn conditional rest value)
      (running : q.current.status = .running c)
      (activation : c.frame.activation = x.a)
      (waiting : c.frame.waiting = none)
      (unwinding : c.frame.unwinding = none)
      (shape : c.frame.remaining = .leaf (.drop site (.local slot) fn conditional []) :: rest)
      (cell : c.store.cells ⟨x.a,slot,[]⟩ = some value)
      (result :
        let e : PV_W1_LeafBoundary.Entry :=
          ⟨c.store,x.a,c.callers,c.frame.loops,rest,fn,[value],slot,q.suspended⟩
        let s := PV_W1_ArgumentEffects.finalStore (base x) e q.current.world
          (x.changes e q.current.world)
        let reply := PV_THR2_ChildBoundary.delivered (base x)
          (PV_FN_THREAD_LocalDrop.pending s x.a slot c.callers c.frame.loops rest fn value)
          (PV_FN_THREAD_LocalDrop.wait slot fn value)
          ((handler x) (.drop fn value) q.current.world)
        r = ⟨⟨reply.status,reply.world,q.current.events ++ reply.events⟩,q.suspended⟩)
      (tail : Run x r out) : Run x q out

/-- Reachability forgets only the finite certificate, never source cells. -/
def Execution (x : Input) (q out : State) : Prop := Nonempty (Run x q out)

/-- Source checkpoints of THIS composition; callee internals are covered by
their own provider contracts, rather than replayed as caller instructions. -/
def checkpoints {x : Input} {q out : State} : Run x q out → List State
  | .refl q => [q]
  | .source q _ _ _ _ tail => q :: checkpoints tail
  | .native q _ _ _ _ _ _ _ _ _ tail => q :: checkpoints tail
  | .callback q _ _ _ _ _ _ tail => q :: checkpoints tail
  | .initAllocation q _ _ _ _ _ _ tail => q :: checkpoints tail
  | .body q _ _ _ _ _ tail => q :: checkpoints tail
  | .drop q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => q :: checkpoints tail

/-- Named documented semantics at ACTUAL reached entries. Quantifying
ArcClone over arbitrary incompatible stores would incorrectly force all
successful clone replies away; the source trace supplies its entry here.
Neither field asserts that a call or a successful answer occurs. -/
structure DocumentedFacts (x : Input) : Prop where
  atomicNew : ∀ q e, Execution x (entry x) q → AtCall x q e →
    PV_THR2_OffPath.functionId e.callee = some 124 →
    PV_FN_THREAD_f361Provider124Counts.DocumentedFacts
      (input124 x e q.current.world q.current.events) x.native
  arcClone : ∀ q e, Execution x (entry x) q → AtCall x q e →
    PV_THR2_OffPath.functionId e.callee = some 360 →
    PV_THR2_LibrarySemantics_ArcClone.Fact (base x) e x.native q.current.world
      (x.changes e q.current.world)
  /-- thread7: the actual213 typed return, with no fixed handle/address. -/
  thread213 : ∀ q e, Execution x (entry x) q → AtCall x q e →
    PV_THR2_OffPath.functionId e.callee = some 213 →
    ∀ value, (nativeReply x q e).answer = .returned (.ok value) →
      PV_THR2_TypedRepresentation_Thread.Shape value
  /-- Shape of the DELIVERED214 value, after the named clone interpretation;
  no shape is imposed on the discarded unrestricted backend payload. -/
  thread214 : ∀ q e, Execution x (entry x) q → AtCall x q e →
    PV_THR2_OffPath.functionId e.callee = some 214 →
    ∀ value, (nativeReply x q e).answer = .returned (.ok value) →
      PV_THR2_TypedRepresentation_Thread.Shape value
  unique612 : PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612.Fact x.native
  bridge14756 : PV_THR2_OwnInitBridgeTypedRepresentation.Facts
    (base x) x.K (fun _ => none) x.resources x.encode (handler x) x.sourceStep

def At (x : Input) (nodes : List PV_STX2_SliceSyntax.Node) (q : State) : Prop :=
  ∃ c, q.current.status = .running c ∧ c.frame.activation = x.a ∧
    PV_THR2_IntrinsicAtContinuation.Ready nodes c

def Returned (x : Input) (q : State) : Prop :=
  ∃ s, q.current.status = .running ⟨{x.parent with waiting := none},x.parents,s⟩ ∧
    q.suspended = x.stack

def Finished (x : Input) (q : State) : Prop :=
  Returned x q ∨ PV_FN_THREAD_NonreturnFrontier.Frozen q

/-- The actual14756 conclusion, including the real source callback, derived
bridged decode, complete post-world and SourceInitBoxOwnership export. These
are conclusions of the OwnInit join, never DocumentedFacts or entry premises. -/
def OwnInit (x : Input) (q : State) : Prop :=
  ∃ (c : Config) (allocationStore sourceStore : Store Data) (w : OWNER)
      (backend : PV_STX_World.World) (handle data : Pointer)
      (callbackBefore registrationBefore : State) (callbackEntry : PV_W1_LeafBoundary.Entry),
    Execution x (entry x) callbackBefore ∧ AtCall x callbackBefore callbackEntry ∧
    callbackEntry.callee = callbackFn ∧ allocationStore = callbackEntry.store ∧
    w = callbackBefore.current.world ∧
    Execution x
      (PV_W1_LeafBoundary.deliver (base x) callbackEntry
        (PV_THR2_ClosureBoxAllocation.reply x.resources x.encode allocationStore w)
        callbackBefore.current.events) registrationBefore ∧
    registrationBefore.current.status = .running
      ⟨{activation := x.a,remaining := PV_THR2_F361.live.body.drop 113},
        x.parent :: x.parents,sourceStore⟩ ∧
    Execution x registrationBefore q ∧
    At x (PV_THR2_F361.live.body.drop 129) q ∧
    q.current.status = .running c ∧
    (x.resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize) (world w)).answer =
      .returned (.ok data.val) ∧ data.val ≠ 0 ∧
    q.current.world = withWorld
      (PV_THR2_BindingRegister.register
        ⟨{activation := x.a,remaining := PV_THR2_F361.live.body.drop 113},
          x.parent :: x.parents,sourceStore⟩
        (PV_THR2_ClosureBoxAllocation.reply x.resources x.encode allocationStore w).world) backend ∧
    let payload := PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
      [PV_THR2_OwnInitPointerCodec.encode handle,
        PV_THR2_BoxDynRepresentationBridge.callback
          (PV_THR2_BoxDynBinaryLayout.symbols x.loadBias x.siteIndex)
          (PV_THR2_PacketBoxBacking.root allocationStore)]
    let words : PV_OWN2_ThreadInitLayout.InitWords :=
      ⟨handle,data,PV_THR2_BoxDynBinaryLayout.runtimeAddress x.loadBias x.siteIndex⟩
    c.store.cells ⟨x.a,46,[]⟩ = some payload ∧
    PV_THR2_OwnInitSourceCodec.decodeBridged q.current.world payload = some words ∧
    x.sourceStep (x.sourceStep q) =
      PV_THR2_OwnInitInterpreterBridged.advance (base x) x.K (fun _ => none)
        x.resources x.encode (handler x) 2 q ∧
    let H := PV_THR2_OwnInitAllocationHandlerBridged.handler x.resources x.encode (handler x)
    let r := H (.child PV_THR2_Source361InitChildren.fnAllocationFull
      c.store.nextActivation [payload]) q.current.world
    let post := PV_THR2_OwnInitInterpreterBridged.advance (base x) x.K
      (fun _ => none) x.resources x.encode (handler x)
      (PV_THR2_Source361AllocationFull.steps (base x) q) q
    PV_THR2_OwnInitAllocationCases.Outcome ⟨x.a,[45]⟩ words
      (x.resources (.malloc 24) (world q.current.world)).answer
      {r with world := post.current.world} ∧
    (∀ cid ch, receiver q.current.world ⟨x.a,[39]⟩ = some (cid,ch) →
      PV_OWN2_ExportContracts.SourceOwnership
        (Attr := Unit) (Data := Unit) (Native := Unit) (IoError := Unit)
        (OsString := Unit) (Scope := Unit) x.resources x.encode x.granted
        ⟨x.a,[39]⟩ ⟨x.a,[45]⟩ cid q.current.world.next ch
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8))

def Frame (x : Input) (q : State) : Prop :=
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed q.current.world
    (PV_W1_LeafBoundary.statusStore q.current.status).nextActivation ∧
  q.suspended = x.stack ∧ (∃ suffix, q.current.events = x.es ++ suffix) ∧
  (∀ c, q.current.status = .running c → Returned x q ∨
    ∃ frames, c.frame :: c.callers = frames ++ (x.parent :: x.parents)) ∧
  ∀ p : Address, p.activation < x.a →
    p ≠ ⟨x.parent.activation,x.dest,[]⟩ →
    ¬ PV_W1_ArgumentEffects.Writable (base x)
      ⟨x.s,x.a,x.parent :: x.parents,[],[],.null,
        [x.threadName,x.stackSize,x.noHooks,x.scope,x.captured],x.dest,x.stack⟩ x.w p →
    (PV_W1_LeafBoundary.statusStore q.current.status).cells p = x.s.cells p

/-- Ownership is recorded on the SAME finite composition that reaches the
return/frontier, per slice2'. There is no global reachable-control invariant. -/
def Checked {x : Input} {q out : State} (run : Run x q out) : Prop :=
  ∀ r, r ∈ checkpoints run → At x (PV_THR2_F361.live.body.drop 129) r → OwnInit x r

/-- Total all-answer specification over the actual composed trace. The
handler and store-effect environment remain arbitrary parameters, so no reply
branch is discarded by selecting one certificate for that environment. -/
def Post (x : Input) : Prop :=
  ∃ (q : State) (run : Run x (entry x) q), Finished x q ∧ Frame x q ∧ Checked run

#print axioms Pre
#print axioms DocumentedFacts
#print axioms Post
end PV_FN_THREAD_f361
