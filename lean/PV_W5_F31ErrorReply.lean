import PV_W5_F31ErrorCall
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31ErrorReply
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine PV_W5_F31ErrorCall

def received (D : Carrier OWNER Data) (s : Store Data) (parents : List Frame)
    (a : Nat) (error : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (prior : List PV_RJ4IDB.NativeEvent) :=
  let c := called s parents a error
  PV_STX2_SlicePrefixEvents.prepend prior
    (adopt c after (PV_STX2_Pinned.reply D (native c []) (waiting s error) r))

theorem reply1 (resources : Resources) (encode : Encode)
    (D : Carrier OWNER Data) (K : Control) (H : PV_W5_F35Modes.HType)
    (s : Store Data) (parents : List Frame) (a : Nat) (error : Data) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) :
    PV_STX2_Source7IterationBindings.advance resources encode D K (fun _ => none) H 1
      ⟨.running (called s parents a error),w,prior⟩ =
      received D s parents a error (H (.child PV_W5_NativeLeaves.callee_f36 s.nextActivation [error]) w) prior := by
  let c := called s parents a error
  have same : PV_STX2_Source7IterationBindings.step resources encode D K (fun _ => none) H c w =
      PV_STX2_SliceMachine.step D K (fun _ => none) H c w := by
    unfold PV_STX2_Source7IterationBindings.step
    rw [PV_STX2_IterationHandlerLocal.bindings2_step D K (fun _ => none) _ H c w (by
      intro q hq
      change some _=some q at hq
      cases hq
      cases error <;> rfl)]
    exact PV_STX2_Source7QUniformAgreement2.neutral D K (fun _ => none) H c w ⟨True.intro,rfl⟩
  change PV_STX2_Source7IterationBindings.advance resources encode D K (fun _ => none) H 1
    ⟨.running c,w,prior⟩ = _
  simp only [PV_STX2_Source7IterationBindings.advance,same]
  rfl

theorem source5 (resources : Resources) (encode : Encode)
    (D : Carrier OWNER Data) (K : Control) (H : PV_W5_F35Modes.HType)
    (s : Store Data) (parents : List Frame) (a : Nat) (error : Data) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent)
    (input : s.cells ⟨a,4,[]⟩=some (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error]))
    (variant : K.variant (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error])=some 1)
    (field : D.field (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error]) 0=some error)
    (replace : D.replaceField (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error]) 0 none=some moved) :
    PV_STX2_Source7IterationBindings.advance resources encode D K (fun _ => none) H 5
      ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body.drop 7},parents,s⟩,w,prior⟩ =
      received D s parents a error (H (.child PV_W5_NativeLeaves.callee_f36 s.nextActivation [error]) w) prior := by
  have first := congrArg (PV_STX2_SlicePrefixEvents.prepend prior)
    (PV_W5_F31ErrorCall.source4 resources encode D K H s parents a error w input variant field replace)
  rw [←PV_STX2_CallSummaryEvents.advance_prepend] at first
  simp only [PV_STX2_SlicePrefixEvents.prepend,List.append_nil] at first
  rw [show 5=4+1 by omega,PV_STX2_Source7IterationBindings.advance_add,first]
  exact reply1 resources encode D K H s parents a error w prior

#print axioms source5

def entry (s : Store Data) (parents : List Frame) (a : Nat) (error : Data) : PV_W5_LeafBoundary.Entry :=
  ⟨prepared s a,a,parents,[],after,[error],8⟩

/-- The actual f36 call instantiates the CLOSED opaque leaf contract. -/
theorem instantiated (D : Carrier OWNER Data) (s : Store Data) (parents : List Frame)
    (a : Nat) (error : Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (backend : PV_W5_NativeFrame.Backend)
    (wf : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed w s.nextActivation) :
    PV_W5_LeafBoundary.Post D (entry s parents a error) PV_W5_NativeLeaves.callee_f36 backend w prior :=
  PV_W5_NativeLeaves.f36 D (entry s parents a error) backend w prior wf

/-- Source and generic leaf stores agree on every answer. The source's exact
waiting record and retained cleanup remain in received, never replaced. -/
theorem leaf_store (D : Carrier OWNER Data) (s : Store Data) (parents : List Frame)
    (a : Nat) (error : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (prior : List PV_RJ4IDB.NativeEvent) :
    PV_W5_LeafBoundary.statusStore (received D s parents a error r prior).status =
    PV_W5_LeafBoundary.statusStore
      (PV_W5_LeafBoundary.deliver D (entry s parents a error) PV_W5_NativeLeaves.callee_f36 r prior).status := by
  rcases r with ⟨answer,post,events⟩
  cases answer with
  | pending => rfl
  | fault f => cases f <;> rfl
  | returned result => cases result <;> cases parents <;> rfl

theorem world_events (D : Carrier OWNER Data) (s : Store Data) (parents : List Frame)
    (a : Nat) (error : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (prior : List PV_RJ4IDB.NativeEvent) :
    (received D s parents a error r prior).world=r.world ∧
    (received D s parents a error r prior).events=prior++r.events := by
  rcases r with ⟨answer,post,events⟩
  cases answer with
  | pending => exact ⟨rfl,rfl⟩
  | fault f => cases f <;> exact ⟨rfl,rfl⟩
  | returned result => cases result <;> cases parents <;> exact ⟨rfl,rfl⟩

theorem source_frame (D : Carrier OWNER Data) (s : Store Data) (parents : List Frame)
    (a : Nat) (error : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (prior : List PV_RJ4IDB.NativeEvent) :
    PV_W5_F59Frame.StoreFrame s (PV_W5_LeafBoundary.statusStore (received D s parents a error r prior).status) a := by
  constructor
  · rcases r with ⟨answer,post,events⟩
    cases answer with
    | pending => exact Nat.le_succ _
    | fault f => cases f <;> exact Nat.le_succ _
    | returned result => cases result <;> cases parents <;> exact Nat.le_succ _
  · intro p outside older
    have fresh : p.activation≠s.nextActivation := Nat.ne_of_lt older
    rcases p with ⟨pa,pi,pp⟩
    change pa≠a at outside
    change pa≠s.nextActivation at fresh
    rcases r with ⟨answer,post,events⟩
    cases answer with
    | pending =>
      change (issued s a error).cells _=s.cells _
      rw [issued,PV_W5_LeafBoundary.arguments_frame _ _ _ _ _ fresh]
      simp [prepared,write,outside]
    | fault f =>
      cases f <;> change (issued s a error).cells _=s.cells _
      all_goals
        rw [issued,PV_W5_LeafBoundary.arguments_frame _ _ _ _ _ fresh]
        simp [prepared,write,outside]
    | returned result =>
      cases result with
      | ok v =>
        change (write (write (issued s a error) ⟨s.nextActivation,0,[]⟩ (some v)) ⟨a,8,[]⟩ (some v)).cells _=s.cells _
        simp only [write]
        simp only [Address.mk.injEq,outside,fresh,false_and,ite_false]
        rw [issued,PV_W5_LeafBoundary.arguments_frame _ _ _ _ _ fresh]
        simp [prepared,write,outside]
      | fail e =>
        cases parents <;> change (issued s a error).cells _=s.cells _
        all_goals
          rw [issued,PV_W5_LeafBoundary.arguments_frame _ _ _ _ _ fresh]
          simp [prepared,write,outside]
      | div =>
        cases parents <;> change (issued s a error).cells _=s.cells _
        all_goals
          rw [issued,PV_W5_LeafBoundary.arguments_frame _ _ _ _ _ fresh]
          simp [prepared,write,outside]

theorem handler_f36 (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parents : List Frame) (a n activation : Nat)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (error : Data) (w : OWNER) :
    PV_FN_SLICE_f31.handler resources encode base ctrl s parents a n external backend
      (.child PV_W5_NativeLeaves.callee_f36 activation [error]) w =
    PV_STX2_Source7QUniformResourceHandler.lift backend
      (.child PV_W5_NativeLeaves.callee_f36 activation [error]) w := by
  unfold PV_FN_SLICE_f31.handler
  rw [if_neg (by
    intro bad
    have ids := congrArg (fun q : PV_STX2_Native.Request Data => match q with
      | .child callee _ _ => PV_STX2_ChainCaptures.regular callee
      | _ => none) bad
    change (some (36 : Nat))=some 35 at ids
    cases ids)]

theorem received_ok (D : Carrier OWNER Data) (s : Store Data) (parents : List Frame)
    (a : Nat) (error value : Data) (w : OWNER) (events prior : List PV_RJ4IDB.NativeEvent) :
    received D s parents a error ⟨.returned (.ok value),w,events⟩ prior =
      ⟨.running ⟨{activation:=a,remaining:=after},parents,
        PV_W5_LeafBoundary.returnedStore (entry s parents a error) value⟩,w,prior++events⟩ := rfl

theorem exceptional_boundary (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (root s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (D : Carrier OWNER Data) (error : Data) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (prior : List PV_RJ4IDB.NativeEvent) (counter : s.nextActivation=root.nextActivation+1)
    (exceptional : ∀ value, r.answer≠.returned (.ok value)) :
    PV_FN_SLICE_f31.Boundary resources encode base ctrl root parent parents a n w external backend
      (received D s (parent::parents) a error r prior) := by
  unfold PV_FN_SLICE_f31.Boundary
  rcases r with ⟨answer,post,events⟩
  cases answer with
  | pending =>
    refine ⟨rfl,rfl,_,rfl,Or.inr ⟨error,?_⟩⟩
    change PV_STX2_Native.Request.child PV_W5_NativeLeaves.callee_f36 s.nextActivation [error] =
      .child PV_W5_NativeLeaves.callee_f36 (root.nextActivation+1) [error]
    rw [counter]
  | fault f => cases f <;> trivial
  | returned result =>
    cases result with
    | ok v => exact False.elim (exceptional v rfl)
    | fail e => exact ⟨rfl,rfl,True.intro⟩
    | div => exact ⟨rfl,rfl,True.intro⟩

#print axioms received_ok
#print axioms exceptional_boundary

#print axioms handler_f36

#print axioms world_events
#print axioms source_frame

#print axioms reply1
#print axioms instantiated
#print axioms leaf_store
end PV_W5_F31ErrorReply
