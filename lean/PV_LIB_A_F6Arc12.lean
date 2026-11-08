import PV_LIB_A_F6Data12
import PV_LIB_A_StructuredTrace12
import PV_THR2_IntrinsicChildCall
import PV_THR2_IntrinsicFrameOrdinary
import PV_THR2_ScopeArcReply
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6Arc12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

def chain : PV_THR2_IntrinsicFrameChain.Chain :=
  PV_LIB_A_F6Prefix11.prepend PV_THR2_F6.node22
    (PV_LIB_A_F6Prefix11.prepend PV_THR2_F6.node23
      (PV_LIB_A_F6Prefix11.prepend PV_THR2_F6.node24 .done))

theorem shape : PV_THR2_IntrinsicFrameChain.nodes chain ++ PV_THR2_F6.live.body.drop 25 =
    PV_THR2_F6.live.body.drop 22 := rfl

theorem sites : PV_LIB_A_ChainTrace11.Sites chain := by
  change (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ (6 : Nat) ≠ 361 ∧ True
  decide

def storageCost (C : Carrier OWNER Data) (c : Config) (w : OWNER) :=
  PV_THR2_IntrinsicFrameChain.steps C c.frame.activation w chain c.store

def storageFinish (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) : State :=
  ⟨⟨PV_THR2_IntrinsicFrameChain.result C c.frame.activation c.callers c.frame.loops
    (PV_THR2_F6.live.body.drop 25) w chain c.store,w,es⟩,stack⟩

def storageSteps (C : Carrier OWNER Data) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F6.live.body.drop 22) (storageCost C) q

def storageAfter (C : Carrier OWNER Data) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F6.live.body.drop 22) (storageFinish C) q

theorem storage (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (storageSteps C q) ⟨q,none⟩ = ⟨storageAfter C q,none⟩ := by
  apply PV_LIB_A_Continuation12.run
  · intro c w es stack h
    rw [PV_THR2_IntrinsicAtContinuation.frame c h]
    change Trace C K P H (PV_THR2_IntrinsicFrameChain.steps C c.frame.activation w chain c.store)
      ⟨⟨.running ⟨{activation := c.frame.activation,remaining := PV_THR2_F6.live.body.drop 22,loops := c.frame.loops},c.callers,c.store⟩,w,es⟩,stack⟩
    rw [← shape]
    exact PV_LIB_A_ChainTrace11.trace C K P H chain _ _ _ _ _ w es stack sites
  · intro c w es stack h
    rw [PV_THR2_IntrinsicAtContinuation.frame c h]
    change PV_THR2_IntrinsicState.advance C K P H
      (PV_THR2_IntrinsicFrameChain.steps C c.frame.activation w chain c.store)
      ⟨⟨.running ⟨{activation := c.frame.activation,remaining := PV_THR2_F6.live.body.drop 22,loops := c.frame.loops},c.callers,c.store⟩,w,es⟩,stack⟩ = _
    rw [← shape]
    exact PV_THR2_IntrinsicFrameChain.run C K P H chain _ _ _ _ _ w es stack

/-- Exact1916 source descriptor and arguments, not a chosen Arc input. -/
def source : PV_STX2_Syntax.Site × Data × Data × List Operand × Nat := match PV_THR2_F6.node25 with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) => (site,kind,generics,args,dest)
  | _ => (⟨0,0,.null⟩,.null,.null,[],0)

def cost (C : Carrier OWNER Data) (c : Config) (w : OWNER) :=
  PV_THR2_IntrinsicChildCall.steps C c.store c.frame.activation source.2.2.2.1 w

def finish (C : Carrier OWNER Data) (H : Handler) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_THR2_IntrinsicChildCall.after C H c.store c.frame.activation c.callers c.frame.loops
    (PV_THR2_F6.live.body.drop 26) source.1 PV_THR2_ScopeArcCall.fn source.2.2.2.1 source.2.2.2.2 w es stack

def steps (C : Carrier OWNER Data) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F6.live.body.drop 25) (cost C) q

def after (C : Carrier OWNER Data) (H : Handler) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F6.live.body.drop 25) (finish C H) q

theorem waiting (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (vs : List Data) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet (PV_THR2_ScopeChildren.table P) ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending s a parents loops
      (PV_THR2_F6.live.body.drop 26) PV_THR2_ScopeArcCall.fn vs 3),w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc
    unfold sourceSelect
    change (match PV_THR2_ScopeChildren.table P PV_THR2_ScopeArcCall.fn with
      | some _ => none | none => none) = none
    rw [show PV_THR2_ScopeChildren.table P PV_THR2_ScopeArcCall.fn = none from
      (PV_THR2_ScopeChildren.children P).2.2.2]
  · intro c hc; cases hc
    cases vs with
    | nil => exact ⟨rfl,rfl,True.intro⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩

theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (q : State) :
    Trace C K (PV_THR2_ScopeChildren.table P) H (steps C q) q := by
  apply PV_LIB_A_Continuation12.trace
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change Trace C K _ H (PV_THR2_IntrinsicChildCall.steps C s a source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.node25 :: PV_THR2_F6.live.body.drop 26,loops := loops},parents,s⟩,w,es⟩,stack⟩
  unfold PV_THR2_IntrinsicChildCall.steps
  apply append C K _ H 1 _ _ ⟨PV_LIB_A_StructuredTrace12.issue_quiet _ s a parents loops _ source.1 _ source.2.2.2.1 source.2.2.2.2 (by decide) w es stack,True.intro⟩
  have issued := PV_THR2_IntrinsicFrameCall.run C K (PV_THR2_ScopeChildren.table P) H s a parents loops
    (PV_THR2_F6.live.body.drop 26) source.1 source.2.1 source.2.2.1 source.2.2.2.1 source.2.2.2.2 w es stack (by rfl)
  change PV_THR2_IntrinsicState.advance C K (PV_THR2_ScopeChildren.table P) H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.node25 :: PV_THR2_F6.live.body.drop 26,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _ at issued
  change Trace C K (PV_THR2_ScopeChildren.table P) H
    (match operands C w a source.2.2.2.1 s with | none => 0 | some _ => 1)
    (PV_THR2_IntrinsicState.advance C K (PV_THR2_ScopeChildren.table P) H 1
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.node25 :: PV_THR2_F6.live.body.drop 26,loops := loops},parents,s⟩,w,es⟩,stack⟩)
  rw [issued]
  unfold PV_THR2_IntrinsicFrameCall.after
  cases he : operands C w a source.2.2.2.1 s with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    exact ⟨waiting P t a parents loops vs w es stack,True.intro⟩

/-- Actual Arc124 boundary, every reply and every failed operand retained.
This is source transport, not an installed native Arc value/physical layout law. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (PV_THR2_ScopeChildren.table P) resources encode H values (steps C q) ⟨q,none⟩ =
      ⟨after C H q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K _ resources encode H values _ _ (trace C K P H q)]
  apply congrArg (fun q => (⟨q,none⟩ : SourceState))
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  exact PV_THR2_IntrinsicChildCall.run C K _ H s a parents loops _ source.1 source.2.1 source.2.2.1 source.2.2.2.1 source.2.2.2.2 w es stack (by rfl)
    (by intro t vs; apply PV_THR2_IntrinsicFrameOrdinary.run; intro heq; have ids := congrArg PV_THR2_OffPath.functionId heq; cases ids)
    (PV_THR2_ScopeChildren.children P).2.2.2

#print axioms shape
#print axioms sites
#print axioms storage
#print axioms waiting
#print axioms trace
#print axioms run
end PV_LIB_A_F6Arc12
