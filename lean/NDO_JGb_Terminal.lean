import NDO_JGa_TerminalParts
import NDO_JGb_ZeroPoint
import NDO_FIv_TerminalValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_Terminal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

/-- Exact native terminal arithmetic for the retained challenge tuple and SAME
composition tuple. The composition return remains explicit. -/
theorem source (selected : Array field.QM31 84#usize) (c1 : Array field.QM31 16#usize)
    (mask : Array field.QM31 10#usize) (comp g h active : field.QM31)
    (hcomp : composition_parts JFu_PublicSemantic.value selected JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_TerminalPrefix.challenges.theta=ok (.Ok (comp,c1,mask,g,h,active)))
    (hc : Canon comp) (hh : Canon h) (ha : Canon active) :
    ∃ out,terminal_parts JFu_PublicSemantic.value selected JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_TerminalPrefix.challenges.theta JFu_TerminalPrefix.challenges.zc
      JFu_TerminalPrefix.challenges.mu=ok (.Ok (out,c1,mask,g)) ∧ Canon out ∧
      decode out=FIv_TerminalValue.formula
        (FIv_EqualityValue.weight JFu_TerminalPrefix.challenges.zc JFu_TerminalPrefix.alpha)
        (decode comp) (decode JFu_TerminalPrefix.challenges.mu) (decode h) (decode active) := by
  obtain ⟨out,call,hout⟩ := JGa_TerminalParts.source JFu_PublicSemantic.value selected
    JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges.zc
    JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
    JFu_TerminalPrefix.challenges.theta JFu_TerminalPrefix.challenges.mu comp c1 mask g h active
    hcomp JFy_PointCanonical.source JGb_ZeroPoint.source hc JGb_Challenges.mu hh ha
  obtain ⟨comp1,h1,active1,called,⟨calls⟩⟩ := FIv_TerminalTrace.reached _ _ _ _ _ _ _ _ _ _ _ _ call
  have same := core.result.Result.Ok.inj (Result.ok.inj (called.symm.trans hcomp))
  have ec := congrArg Prod.fst same
  have eh := congrArg (fun t => t.2.2.2.2.1) same
  have ea := congrArg (fun t => t.2.2.2.2.2) same
  dsimp only at ec eh ea
  subst comp1 h1 active1
  exact ⟨out,call,hout,(FIv_TerminalValue.arithmetic _ _ _ _ _ _ out calls
    JGb_ZeroPoint.source JFy_PointCanonical.source JGb_Challenges.mu hc hh ha).2⟩
#print axioms source
end AspisR1.JGb_Terminal
end
