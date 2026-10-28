import NDO_JGb_Terminal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGb_PublicTerminal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem source (selected : Array field.QM31 84#usize) (c1 : Array field.QM31 16#usize)
    (mask : Array field.QM31 10#usize) (comp g h active : field.QM31)
    (hprefix : r0.Public.terminal_qm31 (FIq_Carriers.toPublic JFs_PublicSerialization.value)
      JFu_TerminalCallback.claims JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges=
      JFu_TerminalPrefix.tail selected)
    (hcomp : composition_parts JFu_PublicSemantic.value selected JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_TerminalPrefix.challenges.theta=ok (.Ok (comp,c1,mask,g,h,active)))
    (hc : Canon comp) (hh : Canon h) (ha : Canon active) :
    ∃ out,r0.Public.terminal_qm31 (FIq_Carriers.toPublic JFs_PublicSerialization.value)
      JFu_TerminalCallback.claims JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges=ok (.Ok out) ∧
      Canon out ∧ decode out=FIv_TerminalValue.formula
        (FIv_EqualityValue.weight JFu_TerminalPrefix.challenges.zc JFu_TerminalPrefix.alpha)
        (decode comp) (decode JFu_TerminalPrefix.challenges.mu) (decode h) (decode active) := by
  obtain ⟨out,call,hoc,hov⟩ := JGb_Terminal.source selected c1 mask comp g h active hcomp hc hh ha
  refine ⟨out,?_,hoc,hov⟩
  rw [hprefix]
  unfold JFu_TerminalPrefix.tail
  rw [call,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JGb_PublicTerminal
end
