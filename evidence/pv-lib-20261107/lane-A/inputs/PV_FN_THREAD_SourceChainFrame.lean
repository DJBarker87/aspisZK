import PV_FN_THREAD_ExpressionFrame
set_option autoImplicit false
namespace PV_FN_THREAD_SourceChainFrame
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_LocalSourceFrame
def SafeChain : PV_THR2_IntrinsicFrameChain.Chain → Prop
  | .done => True
  | .storage _ _ _ next => SafeChain next
  | .bind _ (.local _) e next => PV_FN_THREAD_ExpressionFrame.Safe e ∧ SafeChain next
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
        have first := PV_FN_THREAD_ExpressionFrame.bind_frame B s w a n e t p outside safe original
        exact ⟨(ih t tail).1.trans first.1,(ih t tail).2.trans first.2⟩
      | none =>
        simp only [Option.orElse_none]
        cases fallback : PV_STX2_Store.bind (PV_THR2_AggregateCompletion.carrier B) s w a (.local n) e with
        | none => exact ⟨rfl,rfl⟩
        | some t =>
          have first := PV_FN_THREAD_ExpressionFrame.bind_frame _ s w a n e t p outside safe fallback
          exact ⟨(ih t tail).1.trans first.1,(ih t tail).2.trans first.2⟩
#print axioms chain_frame
end PV_FN_THREAD_SourceChainFrame
