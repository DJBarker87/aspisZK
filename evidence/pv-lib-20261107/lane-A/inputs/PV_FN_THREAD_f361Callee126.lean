import PV_FN_THREAD_f126
import PV_FN_THREAD_f361BoxCallees
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Callee126
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f361BoxCallees.Input
/-- Packet dereference and the optional ScopeData dereference have distinct
emitted type instantiations and saved continuations. -/
inductive Call where
  | packet
  | scope
  deriving DecidableEq

def node : Call → PV_STX2_SliceSyntax.Node
  | .packet => PV_THR2_F361.node93
  | .scope => PV_THR2_F361.node103

def fn (c : Call) : Data := PV_W1_NamedLeafBoundary.function (node c)
def destination : Call → Nat | .packet => 29 | .scope => 34

def rest : Call → List PV_STX2_SliceSyntax.Node
  | .packet => PV_THR2_F361.live.body.drop 82
  | .scope => PV_THR2_F361.block113.drop 8 ++ PV_THR2_F361.live.body.drop 85

def pending {E : Type} (x : Input E) (c : Call) (arc : Address) :=
  PV_THR2_IntrinsicFrameEnter.pending x.s x.a x.parents x.loops (rest c)
    (fn c) [PV_STX2_TypedReferences.reference arc .null] (destination c)

def entered {E : Type} (x : Input E) (c : Call) (arc : Address) :=
  PV_THR2_IntrinsicFrameEnter.entered x.s x.a x.parents x.loops (rest c)
    (fn c) [PV_STX2_TypedReferences.reference arc .null] (destination c) PV_THR2_F126.live

def child {E : Type} (x : Input E) (c : Call) (arc : Address) :
    PV_FN_THREAD_f126_ReturnedStage.Input E :=
  { C := x.C,b := x.b,K := x.K,P := x.P,
    H := PV_THR2_OwnUniformResourceHandler.lift x.native,
    s := (entered x c arc).store,a := x.s.nextActivation,dest := destination c,
    parent := (pending x c arc).frame,parents := x.parents,
    wait := PV_THR2_StaticReply.wait x.s (fn c)
      [PV_STX2_TypedReferences.reference arc .null] (destination c),
    ptr := PV_STX2_TypedReferences.reference arc .null,allocator := .null,
    w := x.w,es := x.es,stack := x.stack }

/-- Source argument issuance and minting prove the callee-entry administrative
clauses. The root and its age are local obligations for the caller's preceding
constructor/entry-ownership join, never hypotheses of f361.contract. -/
theorem pre_at_call {E : Type} (x : Input E) (c : Call) (arc p : Address)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation)
    (older : arc.activation < x.s.nextActivation)
    (root : readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.s arc = some (PV_FN_THREAD_f222_EntryOwned.root p)) :
    PV_FN_THREAD_f126.Pre (child x c arc) arc p := by
  refine ⟨⟨?_,rfl,rfl⟩,?_,older,?_,?_⟩
  · simp [child,entered,PV_THR2_IntrinsicFrameEnter.entered,
      PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticCall.issued,
      PV_STX2_Native.arguments,write]
  · unfold readAddress
    have foreign : arc.activation ≠ x.s.nextActivation := Nat.ne_of_lt older
    change ((PV_THR2_StaticCall.issued x.s
      [PV_STX2_TypedReferences.reference arc .null]).cells
      ⟨arc.activation,arc.localIndex,[]⟩ >>= fun v => readFields _ arc.fields v) = _
    unfold PV_THR2_StaticCall.issued
    have framed := PV_W1_ChildStoreFrame.arguments x.s.nextActivation
      [PV_STX2_TypedReferences.reference arc .null] 1
      {x.s with nextActivation := x.s.nextActivation+1}
      (⟨arc.activation,arc.localIndex,[]⟩ : Address) foreign
    exact (congrArg (fun cell => cell >>= fun v =>
      readFields (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) arc.fields v) framed).trans root
  · change x.s.nextActivation < x.s.nextActivation+1
    omega
  · change PV_W1_OwnerWellFormed.OwnerWellFormed x.w (x.s.nextActivation+1)
    exact PV_W1_OwnerWellFormed.counter_mono _ _ _
      ⟨owner.identities,owner.activations⟩ (Nat.le_succ _)

/-- Instantiate the CLOSED126 theorem itself at either actual f361 call.
The complete provider Post retains every answer and its explicit store. -/
theorem at_call {E : Type} (x : Input E) (c : Call) (arc p : Address)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation)
    (older : arc.activation < x.s.nextActivation)
    (root : readAddress (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      x.s arc = some (PV_FN_THREAD_f222_EntryOwned.root p)) :
    PV_FN_THREAD_f126.Post (child x c arc) x.native arc p := by
  have pre := pre_at_call x c arc p owner older root
  exact PV_FN_THREAD_f126.contract (child x c arc) x.native arc p pre

/-- The two exact operand locals differ, as do the type-erased descriptors. -/
def argumentLocal : Call → Nat | .packet => 30 | .scope => 35

theorem emitted (c : Call) :
    PV_THR2_OffPath.functionId (fn c) = some 126 ∧
    ∃ site, node c = .leaf (.call site (fn c)
      [.move (.local (argumentLocal c))] (.local (destination c)) []) := by
  cases c <;> exact ⟨rfl,_,rfl⟩

/-- The arbitrary argument is read from the emitted source local and moved
before the callee's fresh activation is issued. No store reset occurs. -/
theorem evaluated {E : Type} (x : Input E) (c : Call) (arc : Address)
    (cell : x.s.cells ⟨x.a,argumentLocal c,[]⟩ =
      some (PV_STX2_TypedReferences.reference arc .null)) :
    operands (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) x.w x.a
      [.move (.local (argumentLocal c))] x.s =
      some ([PV_STX2_TypedReferences.reference arc .null],
        write x.s ⟨x.a,argumentLocal c,[]⟩ none) := by
  simp only [operands,operand,PV_STX2_Store.read,locate,cell,Option.bind_some,
    writeAddress]
  rfl

#print axioms emitted
#print axioms evaluated

#print axioms pre_at_call
#print axioms at_call
end PV_FN_THREAD_f361Callee126
