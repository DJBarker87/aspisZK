import PV_LIB_A_RangeStartTrace11
import PV_THR2_IntrinsicFrameChain
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ChainTrace11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine
open PV_LIB_A_PrefixMachine11 PV_THR2_IntrinsicFrameChain

/-- No361 registration/operator/allocation instructions in this fragment.
No source store, future read or native result occurs in this certificate. -/
def Sites : Chain → Prop
  | .done => True
  | .storage site _ _ next | .bind site _ _ next => site.function ≠ 361 ∧ Sites next

theorem storage_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : PV_STX2_Syntax.Site) (live : Bool) (slot : Nat)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (off : site.function ≠ 361) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := .leaf (.storage site live slot) :: rest, loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc
    refine ⟨rfl,rfl,?_⟩
    change ¬ (site.function = 361 ∧ _)
    exact fun h => off h.1

theorem bind_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : PV_STX2_Syntax.Site) (dest : PV_STX2_Syntax.Place) (expr : Expr)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (off : site.function ≠ 361) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := .leaf (.bind site dest expr) :: rest, loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc
    refine ⟨rfl,?_,True.intro⟩
    cases expr <;> simp [PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,off]

/-- Structural certificate for the provider's SAME finite instruction chain.
Failed binds stop at their own source site; no successful read is assumed. -/
theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : PV_LIB_StoreActionTable.Handler)
    (chain : Chain) (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (sites : Sites chain) :
    Trace C K P H (steps C a w chain s)
      ⟨⟨.running ⟨{activation := a,remaining := nodes chain ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  induction chain generalizing s with
  | done => trivial
  | storage site live slot next ih =>
    simp only [steps,nodes,List.cons_append]
    apply append C K P H 1 _ _
      ⟨storage_quiet P s a parents loops _ site live slot w es stack sites.1,True.intro⟩
    rw [PV_THR2_IntrinsicFrameSteps.storage]
    exact ih _ sites.2
  | bind site dest expr next ih =>
    simp only [steps,nodes,List.cons_append]
    apply append C K P H 1 _ _
      ⟨bind_quiet P s a parents loops _ site dest expr w es stack sites.1,True.intro⟩
    rw [PV_THR2_IntrinsicFrameBind.run]
    unfold PV_THR2_IntrinsicFrameBind.after
    change Trace C K P H (match bound C s a dest expr w with
      | none => 0 | some t => steps C a w next t)
      (match bound C s a dest expr w with
      | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
      | some t => ⟨⟨.running ⟨{activation := a,remaining := nodes next ++ rest,loops := loops},parents,t⟩,w,es⟩,stack⟩)
    cases hb : bound C s a dest expr w with
    | none => trivial
    | some t => exact ih t sites.2

/-- Reuse the provider's chain theorem BY NAME after ONE trace lift. -/
theorem corrected_run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : PV_EVHB_OwnerHeap.Resources)
    (encode : PV_EVHB_OwnerHeap.Encode) (H : PV_LIB_StoreActionTable.Handler)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER PV_RJ4IDB.NativeEvent)
    (chain : Chain) (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (sites : Sites chain) :
    advance C K P resources encode H values (steps C a w chain s)
      ⟨⟨⟨.running ⟨{activation := a,remaining := nodes chain ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨result C a parents loops rest w chain s,w,es⟩,stack⟩,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values _ _
    (trace C K P H chain s a parents loops rest w es stack sites),
    PV_THR2_IntrinsicFrameChain.run]

#print axioms storage_quiet
#print axioms bind_quiet
#print axioms trace
#print axioms corrected_run
end PV_LIB_A_ChainTrace11
