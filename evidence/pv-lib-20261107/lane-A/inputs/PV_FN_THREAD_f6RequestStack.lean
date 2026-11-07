import PV_FN_THREAD_f6RequestStep
set_option autoImplicit false
namespace PV_FN_THREAD_f6RequestStack
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6RequestStep

/-- A source frame carries only its remaining emitted straight instructions
and its actual saved request. No constraint is placed on stores or replies. -/
def FrameAllowed (allowed : Data → Prop) (f : Frame) : Prop :=
  (∀ n ∈ f.remaining, ∃ i, n = .leaf i ∧ InstructionAllowed allowed i) ∧
  (∀ wait, f.waiting = some wait → WaitingAllowed allowed wait)

def Active (allowed : Data → Prop) (base : List Frame) (c : Config) : Prop :=
  FrameAllowed allowed c.frame ∧
  ∃ middle, c.callers = middle ++ base ∧ ∀ f ∈ middle, FrameAllowed allowed f

/-- First restoration is recorded separately, so the lower arbitrary caller
is never classified as an instruction belonging to the provider's body. -/
def Restored (parent : Frame) (parents : List Frame) (c : Config) : Prop :=
  c.frame = {parent with waiting := none} ∧ c.callers = parents

/-- Adoption retains only source control already justified by the native
request-step theorem. In particular the returned case merely marks completion. -/
theorem adopt {W E : Type} (allowed : Data → Prop) (base : List Frame)
    (c : Config) (rest : List PV_STX2_SliceSyntax.Node)
    (p : PV_STX2_Native.Prefix W E Data)
    (safe : Active allowed base c)
    (tail : ∀ n ∈ rest, ∃ i, n = .leaf i ∧ InstructionAllowed allowed i)
    (native : ∀ d, p.status = .running d →
      ∀ wait, d.waiting = some wait → WaitingAllowed allowed wait) :
    ∀ d, (PV_STX2_SliceMachine.adopt c rest p).status = .running d →
      Active allowed base d := by
  intro d eq
  cases status : p.status with
  | running next =>
    simp only [PV_STX2_SliceMachine.adopt,status] at eq
    cases eq
    exact ⟨⟨tail,native next status⟩,safe.2⟩
  | returned r =>
    simp only [PV_STX2_SliceMachine.adopt,status] at eq
    split at eq
    · cases eq
    · cases eq
      exact safe
  | fault f => simp [PV_STX2_SliceMachine.adopt,status] at eq
  | undefined site => simp [PV_STX2_SliceMachine.adopt,status] at eq

/-- The pinned reply lift preserves the same request provenance, including its
panic-to-abort interpretation. This lemma includes arbitrary post-worlds. -/
theorem pinned_reply {W E : Type} (B : Carrier W Data) (allowed : Data → Prop)
    (c : PV_STX2_Native.Config Data) (wait : PV_STX2_Native.Waiting Data)
    (r : Reply W E Data) (safe : NativeAllowed allowed c)
    (cleanup : wait.unwind = []) :
    ∀ d, (PV_STX2_Pinned.reply B c wait r).status = .running d →
      NativeAllowed allowed d := by
  by_cases panic : r.answer = .fault .panic
  · rcases r with ⟨answer,world,events⟩
    simp only at panic
    subst answer
    intro d eq
    simp [PV_STX2_Pinned.panic_no_unwind] at eq
  · rw [PV_STX2_PinnedRun.nonpanic_reply B c wait r panic]
    exact PV_FN_THREAD_f6RequestStep.reply B allowed c wait r safe cleanup

/-- A single source instruction cannot add an uninventoried request. The source
continuation and the arbitrary lower stack are preserved explicitly. -/
theorem leaf {W E : Type} (B : Carrier W Data)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (allowed : Data → Prop) (base : List Frame) (c : Config) (w : W)
    (i : Instruction) (rest : List PV_STX2_SliceSyntax.Node)
    (safe : Active allowed base c) (waiting : c.frame.waiting = none)
    (head : InstructionAllowed allowed i)
    (tail : ∀ n ∈ rest, ∃ j, n = .leaf j ∧ InstructionAllowed allowed j) :
    ∀ d, (PV_STX2_SliceMachine.adopt c rest
      (PV_STX2_Native.step B H (native c [i]) w)).status = .running d →
      Active allowed base d := by
  apply adopt allowed base c rest _ safe tail
  intro next eq
  exact (PV_FN_THREAD_f6RequestStep.step B H allowed (native c [i]) w
    ⟨by intro j member; exact (List.mem_singleton.mp member) ▸ head,
      by intro wait h; change c.frame.waiting = some wait at h; rw [waiting] at h; cases h⟩ next eq).2

/-- Source dispatch enters only an inventoried emitted body or delivers ONE
arbitrary full reply. The hypothesis describes the resolver, not a future run.
Completed-return administration is kept separate from request issuance. -/
theorem dispatch {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (allowed : Data → Prop) (base : List Frame) (c : Config) (w : W)
    (safe : Active allowed base c) (done : c.frame.completed = none)
    (bodies : ∀ fn program, allowed fn → P fn = some program →
      ∀ n ∈ program.body, ∃ i, n = .leaf i ∧ InstructionAllowed allowed i) :
    ∀ d, (PV_STX2_SliceMachine.step B K P H c w).status = .running d →
      Active allowed base d := by
  intro d eq
  unfold PV_STX2_SliceMachine.step at eq
  simp only [done] at eq
  cases waiting : c.frame.waiting with
  | some wait =>
    have valid := safe.1.2 wait waiting
    rcases valid.1 with ⟨fn,a,args,request,callee⟩
    simp only [waiting,request] at eq
    cases program : P fn with
    | none =>
      simp only [program] at eq
      apply adopt allowed base c c.frame.remaining _ safe safe.1.1 _ d eq
      intro next nativeEq
      exact (pinned_reply B allowed (native c []) wait _
        ⟨(by intro i member; cases member),safe.1.2⟩ valid.2 next nativeEq).2
    | some body =>
      simp only [program] at eq
      cases eq
      refine ⟨⟨bodies fn body callee program,by intro wait h; cases h⟩,?_⟩
      rcases safe.2 with ⟨middle,callers,frames⟩
      refine ⟨c.frame :: middle,by simp only [callers,List.cons_append],?_⟩
      intro f member
      rcases List.mem_cons.mp member with equal | member
      · subst f; exact safe.1
      · exact frames f member
  | none =>
    simp only [waiting] at eq
    cases remaining : c.frame.remaining with
    | nil => simp [remaining] at eq
    | cons node rest =>
      rcases safe.1.1 node (by rw [remaining]; exact List.mem_cons_self) with ⟨i,equal,head⟩
      subst node
      have tail : ∀ n ∈ rest, ∃ j, n = .leaf j ∧ InstructionAllowed allowed j := by
        intro n member
        exact safe.1.1 n (by rw [remaining]; exact List.mem_cons_of_mem _ member)
      simp only [remaining] at eq
      exact leaf B H allowed base c w i rest safe waiting head tail d eq

/-- Successful completion either restores an admitted suspended source frame
or reaches the exact original caller boundary. No instruction of that lower
caller is treated as a provider instruction. -/
theorem completed_ok {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (allowed : Data → Prop) (parent : Frame) (parents : List Frame)
    (c : Config) (w : W) (value : Data)
    (safe : Active allowed (parent :: parents) c)
    (done : c.frame.completed = some (.ok value)) :
    ∀ d, (PV_STX2_SliceMachine.step B K P H c w).status = .running d →
      Active allowed (parent :: parents) d ∨ Restored parent parents d := by
  intro d eq
  rcases safe.2 with ⟨middle,callers,frames⟩
  cases middle with
  | nil =>
    simp only [List.nil_append] at callers
    unfold PV_STX2_SliceMachine.step at eq
    simp only [done,callers] at eq
    cases waiting : parent.waiting with
    | none => simp [waiting] at eq
    | some wait =>
      cases stored : PV_STX2_Native.storeResult B
          (native (⟨parent,parents,c.store⟩ : Config) []) w wait.action value with
      | none =>
        simp [waiting,PV_STX2_SliceMachine.adopt,PV_STX2_Pinned.reply,
          PV_STX2_Pinned.eraseReply,PV_STX2_Native.reply,stored] at eq
      | some store =>
        simp only [waiting,PV_STX2_Pinned.reply,PV_STX2_Pinned.eraseReply,
          PV_STX2_Native.reply,stored,PV_STX2_SliceMachine.adopt] at eq
        cases eq
        exact Or.inr ⟨rfl,rfl⟩
  | cons f rest =>
    have parentSafe : Active allowed (parent :: parents)
        (⟨f,rest ++ parent :: parents,c.store⟩ : Config) := by
      refine ⟨frames f (List.mem_cons_self),⟨rest,rfl,?_⟩⟩
      intro g member
      exact frames g (List.mem_cons_of_mem _ member)
    unfold PV_STX2_SliceMachine.step at eq
    simp only [done,callers,List.cons_append] at eq
    cases waiting : f.waiting with
    | none => simp [waiting] at eq
    | some wait =>
      simp only [waiting] at eq
      apply Or.inl
      apply adopt allowed (parent :: parents) _ f.remaining _ parentSafe parentSafe.1.1 _ d eq
      intro next nativeEq
      exact (pinned_reply B allowed _ wait _
        ⟨(by intro i member; cases member),parentSafe.1.2⟩
        (parentSafe.1.2 wait waiting).2 next nativeEq).2

#print axioms completed_ok
#print axioms dispatch
#print axioms adopt
#print axioms pinned_reply
#print axioms leaf
end PV_FN_THREAD_f6RequestStack
