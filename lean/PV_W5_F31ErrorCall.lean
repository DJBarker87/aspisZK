import PV_W5_F31ErrorShape
import PV_W5_F31Replies
import PV_STX2_ToVecConstructorExtract
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_W5_F31ErrorCall
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine

def after : List PV_STX2_SliceSyntax.Node :=
  PV_STX2_Source7CtorF31.block20.drop 3 ++ PV_STX2_Source7CtorF31.program.body.drop 8
def unwind : List Instruction := match PV_STX2_Source7CtorF31.node10 with
  | .leaf (.call _ _ _ _ cleanup) => cleanup
  | _ => []
def moved : Data := .object [("aggregate-kind",PV_W5_F35ErrorValues.resultKind),
  ("aggregate-slots",.array [.array []])]
def prepared (s : Store Data) (a : Nat) :=
  write (write (write s ⟨a,7,[]⟩ none) ⟨a,4,[]⟩ (some moved)) ⟨a,7,[]⟩ none
def issued (s : Store Data) (a : Nat) (error : Data) :=
  PV_STX2_Native.arguments s.nextActivation [error] 1
    {prepared s a with nextActivation:=s.nextActivation+1}
def waiting (s : Store Data) (error : Data) : PV_STX2_Native.Waiting Data :=
  ⟨.child PV_W5_NativeLeaves.callee_f36 s.nextActivation [error],.child s.nextActivation (.local 8),unwind⟩
def called (s : Store Data) (parents : List Frame) (a : Nat) (error : Data) : Config :=
  ⟨{activation:=a,remaining:=after,waiting:=some (waiting s error)},parents,issued s a error⟩

/-- Only f31's own match, move and call instructions. The child body is never
entered; the next transition consumes its arbitrary full reply. -/
theorem native4 (D : Carrier OWNER Data) (K : Control) (H : PV_W5_F35Modes.HType)
    (s : Store Data) (parents : List Frame) (a : Nat) (error : Data) (w : OWNER)
    (input : s.cells ⟨a,4,[]⟩=some (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error]))
    (variant : K.variant (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error])=some 1)
    (field : D.field (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error]) 0=some error)
    (replace : D.replaceField (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error]) 0 none=some moved) :
    PV_STX2_SliceMachine.advance D K (fun _ => none) H 4
      ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body.drop 7},parents,s⟩,w,[]⟩ =
      ⟨.running (called s parents a error),w,[]⟩ := by
  simp [PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,PV_STX2_Source7CtorF31.program,PV_STX2_Source7CtorF31.block64,
    PV_STX2_Source7CtorF31.node21,PV_STX2_Source7CtorF31.block20,
    PV_STX2_Source7CtorF31.node8,PV_STX2_Source7CtorF31.node9,PV_STX2_Source7CtorF31.node10,
    selectVariant,native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,
    operands,operand,PV_STX2_Store.read,readFields,locate,writeAddress,replaceFields,write,
    PV_STX2_Native.arguments,input,variant,field,replace,prepared,issued,called,waiting,after,
    unwind,PV_W5_NativeLeaves.callee_f36,PV_W5_NativeLeaves.function]
  funext q
  by_cases h : q=(⟨a,7,[]⟩ : Address) <;> simp [h]

/-- Install the own-instruction segment by the named match agreement and
straight-segment transport, without comparing evaluated prefix stores. -/
theorem source4 (resources : Resources) (encode : Encode)
    (D : Carrier OWNER Data) (K : Control) (H : PV_W5_F35Modes.HType)
    (s : Store Data) (parents : List Frame) (a : Nat) (error : Data) (w : OWNER)
    (input : s.cells ⟨a,4,[]⟩=some (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error]))
    (variant : K.variant (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error])=some 1)
    (field : D.field (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error]) 0=some error)
    (replace : D.replaceField (PV_STX2_Aggregates.pack PV_W5_F35ErrorValues.resultKind [error]) 0 none=some moved) :
    PV_STX2_Source7IterationBindings.advance resources encode D K (fun _ => none) H 4
      ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body.drop 7},parents,s⟩,w,[]⟩ =
      ⟨.running (called s parents a error),w,[]⟩ := by
  let c : Config := ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body.drop 7},parents,s⟩
  let next : Prefix OWNER PV_RJ4IDB.NativeEvent :=
    ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.block20++PV_STX2_Source7CtorF31.program.body.drop 8},parents,s⟩,w,[]⟩
  have nativeFirst : PV_STX2_SliceMachine.advance D K (fun _ => none) H 1 ⟨.running c,w,[]⟩=next := by
    simp [PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,c,next,PV_STX2_Source7CtorF31.program,PV_STX2_Source7CtorF31.block64,
      PV_STX2_Source7CtorF31.node21,PV_STX2_Source7CtorF31.block7,selectVariant,
      PV_STX2_Store.read,locate,input,variant]
  have same := PV_STX2_ToVecConstructorExtract.match_step resources encode D K (fun _ => none) H
    s parents (PV_STX2_Source7CtorF31.program.body.drop 8) a w
  have installedFirst : PV_STX2_Source7IterationBindings.advance resources encode D K (fun _ => none) H 1
      ⟨.running c,w,[]⟩=next := by
    change PV_STX2_Source7IterationBindings.step resources encode D K (fun _ => none) H c w = next
    change PV_STX2_Source7IterationBindings.step resources encode D K (fun _ => none) H c w = PV_STX2_SliceMachine.step D K (fun _ => none) H c w at same
    rw [same]
    exact nativeFirst
  have tail := PV_STX2_CallSummaryLast.run resources encode D K (fun _ => none) (fun _ => none) H
    [PV_STX2_Source7CtorF31.node8,PV_STX2_Source7CtorF31.node9]
    (PV_STX2_Source7CtorF31.node10::after) a parents s w []
    (by
      intro node hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl
      all_goals exact Or.inr ⟨_,rfl,True.intro,True.intro⟩)
    (by
      intro node hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl <;> rfl)
    (by intro stored; exact ⟨by change (some (36 : Nat))≠some 31; decide,rfl⟩)
  have old := native4 D K H s parents a error w input variant field replace
  rw [show 4=1+3 by omega,PV_STX2_SliceDriverBuiltin.advance_add,nativeFirst] at old
  rw [show 4=1+3 by omega,PV_STX2_Source7IterationBindings.advance_add,installedFirst]
  exact tail.trans old

#print axioms source4

#print axioms native4
end PV_W5_F31ErrorCall
