import PV_THR2_OwnInitActualReturnedCases
set_option autoImplicit false
namespace PV_THR2_FrameChainResultControl
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- No successful binding is assumed. Whenever a finite retained frame chain
returns running, its control is the named continuation, independently of store. -/
theorem ready {W : Type} (C : Carrier W Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node) (w : W)
    (chain : PV_THR2_IntrinsicFrameChain.Chain) (s : Store Data) (c : Config)
    (out : PV_THR2_IntrinsicFrameChain.result C a parents loops rest w chain s = .running c) :
    PV_THR2_IntrinsicAtContinuation.Ready rest c := by
  induction chain generalizing s with
  | done => cases out; exact ⟨rfl,rfl,rfl,rfl⟩
  | storage site live slot next ih => exact ih _ out
  | bind site dest expr next ih =>
    simp only [PV_THR2_IntrinsicFrameChain.result] at out
    cases h : PV_THR2_IntrinsicFrameChain.bound C s a dest expr w with
    | none => rw [h] at out; cases out
    | some t => rw [h] at out; exact ih _ out
/-- A retained segment does nothing when its actual input is outside the named
source continuation. This is a table-compatibility lemma, not run transport. -/
theorem inactive {W E : Type} (nodes : List PV_STX2_SliceSyntax.Node)
    (finish : Config → W → List E → List Config → PV_THR2_IntrinsicState.State W E)
    (q : PV_THR2_IntrinsicState.State W E)
    (off : ∀ c, q.current.status = .running c → ¬ PV_THR2_IntrinsicAtContinuation.Ready nodes c) :
    PV_THR2_IntrinsicAtContinuation.after nodes finish q = q := by
  classical
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases status with
  | running c => simp only [PV_THR2_IntrinsicAtContinuation.after,if_neg (off c rfl)]
  | returned r s => rfl
  | fault f s => rfl
  | undefined site s => rfl
#print axioms ready
#print axioms inactive
end PV_THR2_FrameChainResultControl
