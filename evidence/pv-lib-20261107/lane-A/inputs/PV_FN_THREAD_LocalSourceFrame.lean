import PV_FN_THREAD_ReceivedFrame
import PV_THR2_IntrinsicFrameChain
set_option autoImplicit false
namespace PV_FN_THREAD_LocalSourceFrame
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Only the current activation can be invalidated by these operand shapes.
Copies and reference construction may read arbitrary reachable caller cells. -/
def SafeOperand : Operand → Prop
  | .move (.local _) => True
  | .move _ => False
  | _ => True
def SafeExpr : Expr → Prop
  | .use o => SafeOperand o
  | .reference _ o | .rawPointer _ o => SafeOperand o
  | _ => False
def CellFrame (s t : Store Data) (p : Address) : Prop :=
  t.cells p = s.cells p ∧ t.nextActivation = s.nextActivation
theorem operand_frame {W : Type} (B : Carrier W Data) (s : Store Data) (w : W)
    (a : Nat) (o : Operand) (v : Data) (t : Store Data) (p : Address)
    (outside : p.activation ≠ a) (safe : SafeOperand o)
    (evaluated : operand B s w a o = some (v,t)) : CellFrame s t p := by
  cases o with
  | constant d =>
    cases val : B.constant d <;> simp_all [operand,CellFrame]
  | copy q =>
    cases val : read B s w a q <;> simp_all [operand,CellFrame]
  | move q =>
    cases q with
    | «local» n =>
      have ne : p ≠ (⟨a,n,[]⟩ : Address) := fun eq => outside (congrArg Address.activation eq)
      cases val : s.cells ⟨a,n,[]⟩ with
      | none => simp [operand,PV_STX2_Store.read,locate,writeAddress,val] at evaluated
      | some value =>
        simp [operand,PV_STX2_Store.read,locate,writeAddress,val] at evaluated
        rcases evaluated with ⟨rfl,rfl⟩
        exact ⟨write_other _ _ _ _ ne,rfl⟩
    | «global» n => cases safe
    | project q r => cases safe
theorem expression_frame {W : Type} (B : Carrier W Data) (s : Store Data) (w : W)
    (a : Nat) (e : Expr) (v : Data) (t : Store Data) (p : Address)
    (outside : p.activation ≠ a) (safe : SafeExpr e)
    (evaluated : evaluate B s w a e = some (v,t)) : CellFrame s t p := by
  cases e with
  | use o => exact operand_frame B s w a o v t p outside safe evaluated
  | reference q o | rawPointer q o =>
    cases addr : locate B s w a q with
    | none => simp [evaluate,addr] at evaluated
    | some addr =>
      cases arg : operand B s w a o with
      | none => simp [evaluate,addr,arg] at evaluated
      | some pair =>
        rcases pair with ⟨m,u⟩
        simp only [evaluate,addr,arg,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at evaluated
        rcases evaluated with ⟨rfl,rfl⟩
        exact operand_frame B s w a o m u p outside safe arg
  | aggregate tag os => cases safe
  | unary op o => cases safe
  | binary op l r => cases safe
  | nullary op => cases safe
/-- A local destination and locally moved operands frame every foreign cell. -/
theorem bind_frame {W : Type} (B : Carrier W Data) (s : Store Data) (w : W)
    (a n : Nat) (e : Expr) (t : Store Data) (p : Address)
    (outside : p.activation ≠ a) (safe : SafeExpr e)
    (bound : PV_STX2_Store.bind B s w a (.local n) e = some t) : CellFrame s t p := by
  cases val : evaluate B s w a e with
  | none => simp [PV_STX2_Store.bind,val] at bound
  | some pair =>
    rcases pair with ⟨v,u⟩
    have previous := expression_frame B s w a e v u p outside safe val
    have ne : p ≠ (⟨a,n,[]⟩ : Address) := fun eq => outside (congrArg Address.activation eq)
    simp [PV_STX2_Store.bind,val,locate,writeAddress] at bound
    subst t
    exact ⟨(write_other _ _ _ _ ne).trans previous.1,previous.2⟩
def SafeChain : PV_THR2_IntrinsicFrameChain.Chain → Prop
  | .done => True
  | .storage _ _ _ next => SafeChain next
  | .bind _ (.local _) e next => SafeExpr e ∧ SafeChain next
  | .bind _ _ _ _ => False
/-- The full explicit store, including a missing-binding terminal, is framed.
This is a shape induction; it does not re-execute a generated source prefix. -/
theorem chain_frame {W : Type} (B : Carrier W Data) (s : Store Data) (w : W)
    (a : Nat) (parents : List PV_STX2_SliceMachine.Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (chain : PV_THR2_IntrinsicFrameChain.Chain)
    (p : Address) (outside : p.activation ≠ a) (safe : SafeChain chain) :
    CellFrame s (PV_FN_THREAD_FullReplyFrame.store
      (PV_THR2_IntrinsicFrameChain.result B a parents loops rest w chain s)) p := by
  induction chain generalizing s with
  | done => exact ⟨rfl,rfl⟩
  | storage site live n next ih =>
    have ne : p ≠ (⟨a,n,[]⟩ : Address) := fun eq => outside (congrArg Address.activation eq)
    exact ⟨(ih _ safe).1.trans (write_other _ _ _ _ ne),(ih _ safe).2⟩
  | bind site dest e next ih =>
    cases dest with
    | «global» n => cases safe
    | project q r => cases safe
    | «local» n =>
      rcases safe with ⟨safe,tail⟩
      unfold PV_THR2_IntrinsicFrameChain.result PV_THR2_IntrinsicFrameChain.bound
      cases original : PV_STX2_Store.bind B s w a (.local n) e with
      | some t =>
        simp only [Option.orElse_some]
        have first := bind_frame B s w a n e t p outside safe original
        exact ⟨(ih t tail).1.trans first.1,(ih t tail).2.trans first.2⟩
      | none =>
        simp only [Option.orElse_none]
        cases fallback : PV_STX2_Store.bind (PV_THR2_AggregateCompletion.carrier B) s w a (.local n) e with
        | none => exact ⟨rfl,rfl⟩
        | some t =>
          have first := bind_frame _ s w a n e t p outside safe fallback
          exact ⟨(ih t tail).1.trans first.1,(ih t tail).2.trans first.2⟩
#print axioms operand_frame
#print axioms expression_frame
#print axioms bind_frame
#print axioms chain_frame
end PV_FN_THREAD_LocalSourceFrame
