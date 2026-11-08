import PV_THR2_CatchChildren
import PV_LIB_A_StructuredTrace12
import PV_THR2_IntrinsicChildCall
import PV_THR2_IntrinsicFrameOrdinary
import PV_THR2_ScopeArcReply
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F219Full13413
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Actual9182 ManuallyDrop134 descriptor and operands, not a substituted wrapper. -/
def source : PV_STX2_Syntax.Site × Data × Data × List Operand × Nat := match PV_THR2_F219.node5 with
  | .leaf (.call site (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) => (site,kind,generics,args,dest)
  | _ => (⟨0,0,.null⟩,.null,.null,[],0)

def fn : Data := .object [("Regular",.object [("kind",source.2.1),("generics",source.2.2.1)])]

def cost (C : Carrier OWNER Data) (c : Config) (w : OWNER) :=
  PV_THR2_IntrinsicChildCall.steps C c.store c.frame.activation source.2.2.2.1 w

def finish (C : Carrier OWNER Data) (H : Handler) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_THR2_IntrinsicChildCall.after C H c.store c.frame.activation c.callers c.frame.loops
    (PV_THR2_F219.live.body.drop 6) source.1 fn source.2.2.2.1 source.2.2.2.2 w es stack

def steps (C : Carrier OWNER Data) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.steps (PV_THR2_F219.live.body.drop 5) (cost C) q

def after (C : Carrier OWNER Data) (H : Handler) (q : State) :=
  PV_THR2_IntrinsicAtContinuation.after (PV_THR2_F219.live.body.drop 5) (finish C H) q

theorem waiting (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (vs : List Data) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet (PV_THR2_CatchChildren.table P) ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending s a parents loops
      (PV_THR2_F219.live.body.drop 6) fn vs 3),w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc
    unfold sourceSelect
    change (match PV_THR2_CatchChildren.table P fn with
      | some _ => none | none => none) = none
    rw [show PV_THR2_CatchChildren.table P fn = none from
      PV_THR2_CatchChildren.child P]
  · intro c hc; cases hc
    cases vs with
    | nil => exact ⟨rfl,rfl,True.intro⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩

theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (q : State) :
    Trace C K (PV_THR2_CatchChildren.table P) H (steps C q) q := by
  apply PV_LIB_A_Continuation12.trace
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change Trace C K _ H (PV_THR2_IntrinsicChildCall.steps C s a source.2.2.2.1 w)
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.node5 :: PV_THR2_F219.live.body.drop 6,loops := loops},parents,s⟩,w,es⟩,stack⟩
  unfold PV_THR2_IntrinsicChildCall.steps
  apply append C K _ H 1 _ _ ⟨PV_LIB_A_StructuredTrace12.issue_quiet _ s a parents loops _ source.1 _ source.2.2.2.1 source.2.2.2.2 (by decide) w es stack,True.intro⟩
  have issued := PV_THR2_IntrinsicFrameCall.run C K (PV_THR2_CatchChildren.table P) H s a parents loops
    (PV_THR2_F219.live.body.drop 6) source.1 source.2.1 source.2.2.1 source.2.2.2.1 source.2.2.2.2 w es stack (by rfl)
  change PV_THR2_IntrinsicState.advance C K (PV_THR2_CatchChildren.table P) H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.node5 :: PV_THR2_F219.live.body.drop 6,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _ at issued
  change Trace C K (PV_THR2_CatchChildren.table P) H
    (match operands C w a source.2.2.2.1 s with | none => 0 | some _ => 1)
    (PV_THR2_IntrinsicState.advance C K (PV_THR2_CatchChildren.table P) H 1
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F219.node5 :: PV_THR2_F219.live.body.drop 6,loops := loops},parents,s⟩,w,es⟩,stack⟩)
  rw [issued]
  unfold PV_THR2_IntrinsicFrameCall.after
  cases he : operands C w a source.2.2.2.1 s with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    exact ⟨waiting P t a parents loops vs w es stack,True.intro⟩

/-- Actual full134 boundary retains every reply and source gap. The named
ManuallyDrop value law is not replaced by this source-history equality. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K (PV_THR2_CatchChildren.table P) resources encode H values (steps C q) ⟨q,none⟩ =
      ⟨after C H q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K _ resources encode H values _ _ (trace C K P H q)]
  apply congrArg (fun q => (⟨q,none⟩ : SourceState))
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  exact PV_THR2_IntrinsicChildCall.run C K _ H s a parents loops _ source.1 source.2.1 source.2.2.1 source.2.2.2.1 source.2.2.2.2 w es stack (by rfl)
    (by intro t vs; apply PV_THR2_IntrinsicFrameOrdinary.run; intro heq; have ids := congrArg PV_THR2_OffPath.functionId heq; cases ids)
    (PV_THR2_CatchChildren.child P)

#print axioms source
#print axioms waiting
#print axioms trace
#print axioms run
end PV_LIB_A_F219Full13413
