import PV_FN_THREAD_f361OwnEntryPrefix
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361OwnEntryProgress
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f361 PV_FN_THREAD_f361OwnEntry
open PV_THR2_IntrinsicFrameChain PV_FN_THREAD_f361JoinStatements

/-- The two genuine outcomes of a straight prefix: its next source cut, or
the exact missing-binding state. This inspects result SHAPE only. -/
theorem chain_shape (x : Input) (source : Chain) (s : Store Data)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) :
    (∃ t, result (base x) x.a (x.parent :: x.parents) [] rest w source s =
      .running ⟨{activation := x.a,remaining := rest},x.parent :: x.parents,t⟩) ∨
    (∃ site t, result (base x) x.a (x.parent :: x.parents) [] rest w source s =
      .undefined site t) := by
  induction source generalizing s with
  | done => exact Or.inl ⟨s,rfl⟩
  | storage site live slot next ih => exact ih _
  | bind site dest expr next ih =>
    cases hb : bound (base x) s x.a dest expr w with
    | none => exact Or.inr ⟨some site,s,by simp only [result,hb]⟩
    | some t => simpa only [result,hb] using ih t

/-- Counter preservation is taken from the already audited source-chain
frame, not recomputed by normalizing the successive concrete stores. -/
theorem chain_counter (x : Input) (source : Chain) (s : Store Data)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER)
    (safe : PV_FN_THREAD_SourceChainFrame.SafeChain source) :
    (PV_W1_LeafBoundary.statusStore
      (result (base x) x.a (x.parent :: x.parents) [] rest w source s)).nextActivation =
        s.nextActivation := by
  exact (PV_FN_THREAD_SourceChainFrame.chain_frame (base x) s w x.a
    (x.parent :: x.parents) [] rest source ⟨x.a+1,0,[]⟩ (by simp) safe).2

/-- Local context and all failure cases at a straight prefix's selected cut.
No claim that the complete own_entry_to124 join has closed is made here. -/
theorem chain_progress (x : Input) (source : Chain) (s : Store Data)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (plain : Plain source)
    (safe : PV_FN_THREAD_SourceChainFrame.SafeChain source)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w s.nextActivation)
    (age : x.a < s.nextActivation) :
    let q := state x s (x.parent :: x.parents) [] (nodes source ++ rest) w es x.stack
    let out : State :=
      ⟨⟨result (base x) x.a (x.parent :: x.parents) [] rest w source s,w,es⟩,x.stack⟩
    Execution x q out ∧ Context x out ∧
      (PV_FN_THREAD_NonreturnFrontier.Frozen out ∨ At x rest out) := by
  intro q out
  have execution := chain x source s (x.parent :: x.parents) [] rest w es x.stack plain
  have counter := chain_counter x source s rest w safe
  have context : Context x out := by
    refine ⟨?_,?_,?_⟩
    · change PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w _
      rw [counter]
      exact owner
    · change x.a < _
      rw [counter]
      exact age
    · intro c status activation
      rcases chain_shape x source s rest w with running | undefined
      · obtain ⟨t,shape⟩ := running
        change result (base x) x.a (x.parent :: x.parents) [] rest w source s = .running c at status
        rw [shape] at status
        cases status
        rfl
      · obtain ⟨site,t,shape⟩ := undefined
        change result (base x) x.a (x.parent :: x.parents) [] rest w source s = .running c at status
        rw [shape] at status
        cases status
  refine ⟨execution,context,?_⟩
  rcases chain_shape x source s rest w with running | undefined
  · obtain ⟨t,shape⟩ := running
    right
    refine ⟨_,shape,rfl,rfl,rfl,rfl,rfl⟩
  · obtain ⟨site,t,shape⟩ := undefined
    left
    intro c status
    change result (base x) x.a (x.parent :: x.parents) [] rest w source s = .running c at status
    rw [shape] at status
    cases status

/-- The native leaf's arbitrary argument-reachable delta changes no activation
counter. Every answer then increments the issued counter exactly once. -/
theorem native_counter (x : Input) (e : PV_W1_LeafBoundary.Entry) (w : OWNER)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) (es : List PV_RJ4IDB.NativeEvent) :
    let d := PV_W1_ArgumentEffects.afterEffects (base x) e w (x.changes e w)
    let out := PV_W1_LeafBoundary.deliver (base x) d r es
    (PV_W1_LeafBoundary.statusStore out.current.status).nextActivation =
      e.store.nextActivation + 1 := by
  intro d out
  have status := (PV_W1_LeafBoundary.full_reply (base x) d r es).1
  rw [status,PV_W1_ClosedLeaves.counter]
  rfl

#print axioms chain_shape
#print axioms chain_counter
#print axioms chain_progress
#print axioms native_counter
end PV_FN_THREAD_f361OwnEntryProgress
