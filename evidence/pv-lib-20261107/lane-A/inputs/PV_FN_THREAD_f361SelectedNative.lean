import PV_FN_THREAD_f361OwnEntryProgress
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361SelectedNative
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f361 PV_FN_THREAD_f361JoinStatements
open scoped Classical

/-- The complete native boundary on an already issued descriptor. No source
operand is re-evaluated and no delta or native answer is selected. -/
def after (x : Input) (q : State) (e : PV_W1_LeafBoundary.Entry) : State :=
  PV_W1_LeafBoundary.deliver (base x)
    (PV_W1_ArgumentEffects.afterEffects (base x) e q.current.world
      (x.changes e q.current.world))
    ((handler x) (.child e.callee e.store.nextActivation e.arguments) q.current.world)
    q.current.events

/-- Exact call-site control excludes the one interpreted clone214 action.
This does not inspect a native answer or an argument value. -/
theorem ordinary_at (x : Input) (q : State) (e : PV_W1_LeafBoundary.Entry)
    (site : Site) (callee : Data) (args : List Operand) (dest : PV_STX2_Syntax.Place)
    (rest : List PV_STX2_SliceSyntax.Node)
    (ready : At x (.leaf (.call site callee args dest []) :: rest) q)
    (notOperator : site.statement ≠ 14535) :
    nativeReply x q e =
      (handler x) (.child e.callee e.store.nextActivation e.arguments) q.current.world := by
  obtain ⟨c,status,activation,remaining,waiting,unwinding,completed⟩ := ready
  have neutral : PV_THR2_OperatorAction.selected c = none := by
    simp [PV_THR2_OperatorAction.selected,completed,waiting,remaining,
      PV_THR2_OperatorAction.instruction,notOperator]
  simp [nativeReply,status,neutral]

/-- Append exactly one native summary edge. The ordinary-reply equation is
a source-control obligation at the selected call, not an entry assumption. -/
def step (x : Input) (q : State) (e : PV_W1_LeafBoundary.Entry)
    (call : AtCall x q e)
    (leaf : PV_THR2_OffPath.functionId e.callee ∉ [some 124,some 126,some 443,some 458])
    (notCallback : e.callee ≠ callbackFn)
    (notInit : e.callee ≠ PV_THR2_Source361InitChildren.fnAllocationFull)
    (ordinary : nativeReply x q e =
      (handler x) (.child e.callee e.store.nextActivation e.arguments) q.current.world) :
    Run x q (after x q e) := by
  apply Run.native q (after x q e) (after x q e) e call leaf notCallback notInit
  · rw [ordinary]
    exact PV_W1_LeafBoundary.full_reply _ _ _ _
  · rw [ordinary]
    rfl
  · exact .refl _

/-- The actual descriptor inherits the caller stack from the selected
context. No claim about arbitrary future calls or states is required. -/
theorem geometry (x : Input) (q : State) (e : PV_W1_LeafBoundary.Entry)
    (call : AtCall x q e) (context : Context x q) :
    e.caller = x.a ∧ e.parents = x.parent :: x.parents := by
  obtain ⟨c,site,args,cleanup,status,activation,waiting,unwinding,shape,
    selected,caller,parents,loops,stack⟩ := call
  exact ⟨caller,parents.trans (context.2.2 c status activation)⟩

/-- All answers preserve OWNER well-formedness at the complete returned
store. Success selects the saved continuation; all other answers are frozen
at this boundary, retaining their world, events and explicit source writes. -/
theorem progress (x : Input) (q : State) (e : PV_W1_LeafBoundary.Entry)
    (call : AtCall x q e) (context : Context x q)
    (age : x.a < e.store.nextActivation)
    (post : PV_W1_ArgumentEffects.Post (base x) e x.native q.current.world
      q.current.events (x.changes e q.current.world)) :
    Context x (after x q e) ∧
      (PV_FN_THREAD_NonreturnFrontier.Frozen (after x q e) ∨
        ∃ value, ((handler x) (.child e.callee e.store.nextActivation e.arguments)
          q.current.world).answer = .returned (.ok value) ∧ At x e.rest (after x q e)) := by
  let d := PV_W1_ArgumentEffects.afterEffects (base x) e q.current.world
    (x.changes e q.current.world)
  let r := (handler x) (.child e.callee e.store.nextActivation e.arguments) q.current.world
  have geo := geometry x q e call context
  have boundary : PV_W1_LeafBoundary.Post d r q.current.events (after x q e) := post.1
  have count : (PV_W1_LeafBoundary.statusStore (after x q e).current.status).nextActivation =
      e.store.nextActivation + 1 :=
    PV_FN_THREAD_f361OwnEntryProgress.native_counter x e q.current.world r q.current.events
  have invariant := post.2.1
  have ctx : Context x (after x q e) := by
    refine ⟨⟨invariant.1,invariant.2⟩,?_,?_⟩
    · rw [count]
      exact Nat.lt_trans age (Nat.lt_succ_self _)
    · intro c status activation
      rw [boundary.1] at status
      cases answer : r.answer with
      | pending =>
        simp only [PV_W1_LeafBoundary.expectedStatus,answer] at status
        cases status
        exact geo.2
      | fault f =>
        simp only [PV_W1_LeafBoundary.expectedStatus,answer] at status
        cases status
      | returned result =>
        cases result with
        | ok value =>
          simp only [PV_W1_LeafBoundary.expectedStatus,answer] at status
          cases status
          exact geo.2
        | fail err =>
          simp only [PV_W1_LeafBoundary.expectedStatus,answer,d,
            PV_W1_ArgumentEffects.afterEffects,geo.2] at status
          cases status
          rfl
        | div =>
          simp only [PV_W1_LeafBoundary.expectedStatus,answer,d,
            PV_W1_ArgumentEffects.afterEffects,geo.2] at status
          cases status
          rfl
  refine ⟨ctx,?_⟩
  by_cases success : ∃ value, r.answer = .returned (.ok value)
  · obtain ⟨value,answer⟩ := success
    right
    refine ⟨value,answer,
      ⟨{activation := e.caller,remaining := e.rest,loops := e.loops},e.parents,
        PV_THR2_StaticReply.returnedStore d.store e.caller e.arguments e.destination value⟩,
      ?_,geo.1,rfl,rfl,rfl,rfl⟩
    exact boundary.1.trans (by
      simp only [PV_W1_LeafBoundary.expectedStatus,answer,d,PV_W1_ArgumentEffects.afterEffects])
  · left
    exact PV_FN_THREAD_NonreturnFrontier.received (base x) d.store e.caller
      e.parents e.loops e.rest e.callee e.arguments e.destination r q.current.events e.suspended
      (by intro value answer; exact success ⟨value,answer⟩)

#print axioms step
#print axioms ordinary_at
#print axioms geometry
#print axioms progress
end PV_FN_THREAD_f361SelectedNative
