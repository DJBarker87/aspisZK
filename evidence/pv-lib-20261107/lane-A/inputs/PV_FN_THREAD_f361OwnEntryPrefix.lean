import PV_FN_THREAD_f361OwnEntry
import PV_FN_THREAD_f361Prefix
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361OwnEntryPrefix
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f361 PV_FN_THREAD_f361OwnEntry
open scoped Classical

theorem prologue_plain : Plain PV_THR2_Source361Prologue.chain := by
  simp [Plain,PV_THR2_Source361Prologue.chain,PV_THR2_Source15CaptureChain.prepend,
    PV_THR2_F361.node0,PV_THR2_F361.node1,PV_THR2_F361.node2,PV_THR2_F361.node3,
    PV_THR2_F361.node4,PV_THR2_F361.node5,PV_THR2_F361.node6,PV_THR2_F361.node7,
    PV_THR2_F361.node8,PV_THR2_F361.node9,PV_THR2_F361.node10,PV_THR2_F361.node11,
    PV_THR2_F361.node12,PV_THR2_F361.node13,PV_THR2_F361.node14,PV_THR2_F361.node15,
    PV_THR2_F361.node16,PV_THR2_F361.node17,PV_THR2_F361.node18,PV_THR2_F361.node19,
    PV_THR2_F361.node20,PV_THR2_F361.node21,
    PV_THR2_OwnUniformNeutral.instruction,PV_THR2_OperatorAction.instruction]

/-- Actual22-node prologue, at own entry, using the existing chain result.
There is no native boundary or store reset in this prefix. -/
theorem prologue (x : Input) :
    Execution x (entry x) (PV_THR2_Source361Prologue.after (base x) (entry x)) := by
  have run := chain x PV_THR2_Source361Prologue.chain x.s (x.parent :: x.parents) []
    (PV_THR2_F361.live.body.drop 22) x.w x.es x.stack prologue_plain
  rw [PV_THR2_Source361Prologue.shape] at run
  have ready : PV_THR2_IntrinsicAtContinuation.Ready PV_THR2_F361.live.body
      ⟨{activation := x.a,remaining := PV_THR2_F361.live.body},x.parent :: x.parents,x.s⟩ :=
    ⟨rfl,rfl,rfl,rfl⟩
  simpa only [PV_THR2_Source361Prologue.after,PV_THR2_IntrinsicAtContinuation.after,
    entry,if_pos ready,PV_THR2_Source361Prologue.finish,state] using run

def fn (kind generics : Data) : Data :=
  .object [("Regular",.object [("kind",kind),("generics",generics)])]

def issued (x : Input) (t : Store Data) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (kind generics : Data)
    (vs : List Data) (dest : Nat) (stack : List Config) : PV_W1_LeafBoundary.Entry :=
  ⟨t,x.a,parents,loops,rest,fn kind generics,vs,dest,stack⟩

/-- Explicit full-memory native boundary expression. This composes the
existing leaf boundary, rather than executing a callee body or silently using
the earlier zero-delta helper result. -/
def nativeAfter (x : Input) (s : Store Data) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (site : Site) (kind generics : Data) (args : List Operand) (dest : Nat)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) : State :=
  let q := state x s parents loops
    (.leaf (.call site (fn kind generics) args (.local dest) []) :: rest) w es stack
  match operands (base x) w x.a args s with
  | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
  | some (vs,t) =>
    let e := issued x t parents loops rest kind generics vs dest stack
    PV_W1_LeafBoundary.deliver (base x)
      (PV_W1_ArgumentEffects.afterEffects (base x) e w (x.changes e w))
      (nativeReply x q e) es

/-- All answers and every native source-memory delta at an actual static
prefix call. The hypotheses are SOURCE SHAPE obligations for this local
generic lemma, never f361 Pre/DocumentedFacts fields. -/
theorem native (x : Input) (s : Store Data) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (site : Site) (kind generics : Data) (args : List Operand) (dest : Nat)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (stable : operands (PV_THR2_AggregateCompletion.carrier (base x)) w x.a args s =
      operands (base x) w x.a args s)
    (notAllocation : site.statement ≠ 14756)
    (notOperator : PV_THR2_OperatorAction.instruction
      (.call site (fn kind generics) args (.local dest) []) = none)
    (leaf : PV_THR2_OffPath.functionId (fn kind generics) ∉ [some 124,some 126,some 443,some 458])
    (notCallback : fn kind generics ≠ callbackFn)
    (notInit : fn kind generics ≠ PV_THR2_Source361InitChildren.fnAllocationFull) :
    Execution x
      (state x s parents loops
        (.leaf (.call site (fn kind generics) args (.local dest) []) :: rest) w es stack)
      (nativeAfter x s parents loops rest site kind generics args dest w es stack) := by
  let q := state x s parents loops
    (.leaf (.call site (fn kind generics) args (.local dest) []) :: rest) w es stack
  cases selected : operands (base x) w x.a args s with
  | none =>
    have agreement := ordinary x q
      (by
        intro c h
        cases h
        simp [state,PV_THR2_OwnInitAction.selected,notAllocation])
      (by intro c h; cases h; exact notOperator)
      (by intro c h; cases h; trivial)
    have core := PV_THR2_IntrinsicFrameCall.run (base x) x.K (fun _ => none)
      (handler x) s x.a parents loops rest site kind generics args dest w es stack stable
    simp only [PV_THR2_IntrinsicFrameCall.after,selected] at core
    have source : SourceOnly x q := by
      intro c h
      cases h
      refine ⟨rfl,rfl,?_,?_⟩
      · intro site' fn' args' dest' cleanup' rest' shape
        cases shape
        exact selected
      · intro site' slot' fn' conditional' cleanup' rest' shape
        cases shape
    have trace : Run x q ⟨⟨.undefined (some site) s,w,es⟩,stack⟩ :=
      .source _ _ _ source (agreement.trans core) (.refl _)
    simpa only [nativeAfter,selected] using (show Execution x q _ from ⟨trace⟩)
  | some pair =>
    rcases pair with ⟨vs,t⟩
    let e := issued x t parents loops rest kind generics vs dest stack
    let d := PV_W1_ArgumentEffects.afterEffects (base x) e w (x.changes e w)
    let r := nativeReply x q e
    let out := PV_W1_LeafBoundary.deliver (base x) d r es
    have actual : AtCall x q e := by
      refine ⟨_,site,args,[],rfl,rfl,rfl,rfl,rfl,selected,rfl,rfl,rfl,rfl⟩
    have post := PV_W1_LeafBoundary.full_reply (base x) d r es
    have trace : Run x q out :=
      .native q out out e actual leaf notCallback notInit post rfl (.refl out)
    simpa only [nativeAfter,selected] using (show Execution x q out from ⟨trace⟩)

#print axioms prologue_plain
#print axioms prologue
#print axioms native
end PV_FN_THREAD_f361OwnEntryPrefix
