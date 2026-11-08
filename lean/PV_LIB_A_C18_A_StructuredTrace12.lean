import PV_LIB_A_C18_A_Continuation12
import PV_LIB_A_C18_A_RangeStartTrace11
import PV_THR2_IntrinsicStructuredCall
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_StructuredTrace12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

theorem issue_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : PV_STX2_Syntax.Site) (fn : Data) (args : List Operand) (dest : Nat) (off : site.function ≠ 361)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := .leaf (.call site fn args (.local dest) []) :: rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc
    refine ⟨?_,?_,True.intro⟩
    · simp [PV_THR2_OwnInitAction.selected,off]
    · simp [PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,off]

theorem enter_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (fn : Data) (vs : List Data) (dest : Nat)
    (body : PV_STX2_SliceSyntax.Program) (resolved : P fn = some body)
    (own : PV_THR2_OwnInitAction.selected (PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest fn vs dest) = false)
    (ordinary : PV_THR2_OperatorAction.selected (PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest fn vs dest) = none)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending s a parents loops rest fn vs dest),w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc
    unfold sourceSelect
    change (match P fn with | some _ => none | none => _) = none
    rw [resolved]
  · intro c hc; cases hc; exact ⟨own,ordinary,True.intro⟩

/-- Structured source calls have no source-leaf action. The failed-operand arm
is still one step to its actual gap; successful operands enter the named body. -/
theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : PV_STX2_Syntax.Site) (kind generics : Data)
    (args : List Operand) (dest : Nat) (body : PV_STX2_SliceSyntax.Program)
    (off : site.function ≠ 361)
    (own : ∀ t vs, PV_THR2_OwnInitAction.selected (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest (.object [("Regular",.object [("kind",kind),("generics",generics)])]) vs dest) = false)
    (ordinary : ∀ t vs, PV_THR2_OperatorAction.selected (PV_THR2_IntrinsicFrameEnter.pending t a parents loops rest (.object [("Regular",.object [("kind",kind),("generics",generics)])]) vs dest) = none)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (stable : operands (PV_THR2_AggregateCompletion.carrier C) w a args s = operands C w a args s)
    (resolved : P (.object [("Regular",.object [("kind",kind),("generics",generics)])]) = some body) :
    Trace C K P H (PV_THR2_IntrinsicStructuredCall.steps C s a args w)
      ⟨⟨.running ⟨{activation := a,remaining := .leaf (.call site
        (.object [("Regular",.object [("kind",kind),("generics",generics)])]) args (.local dest) []) :: rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  unfold PV_THR2_IntrinsicStructuredCall.steps
  apply append C K P H 1 _ _ ⟨issue_quiet P s a parents loops rest site _ args dest off w es stack,True.intro⟩
  rw [PV_THR2_IntrinsicFrameCall.run C K P H s a parents loops rest site kind generics args dest w es stack stable]
  unfold PV_THR2_IntrinsicFrameCall.after
  cases h : operands C w a args s with
  | none => trivial
  | some pair =>
    rcases pair with ⟨vs,t⟩
    exact ⟨enter_quiet P t a parents loops rest _ vs dest body resolved (own t vs) (ordinary t vs) w es stack,True.intro⟩

#print axioms issue_quiet
#print axioms enter_quiet
#print axioms trace
end PV_LIB_A_StructuredTrace12
