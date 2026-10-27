import RPt_JFs_TX2_TailCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_TailQM
open Aeneas Aeneas.Std Result

theorem continued {T : Type} {o : Option T} {v : T}
    (run : FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitTry.branch o=
      ok (core.ops.control_flow.ControlFlow.Continue v)) : o=some v := by
  cases o with
  | none => cases run
  | some a => exact congrArg some (core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj run))

theorem cm {bytes : Slice U8} {o : Option FIp_DotDecode.field.CM31} {v : FIp_DotDecode.field.CM31}
    (decode : FIp_DotDecode.field.CM31.from_le_bytes bytes=ok o)
    (branch : FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitTry.branch o=
      ok (core.ops.control_flow.ControlFlow.Continue v)) : FIo_CMValues.Canon v := by
  rw [continued branch] at decode
  exact JFs_TX2_TailCanonical.cm bytes v decode

theorem qm (bytes : Slice U8) (out : FIp_DotDecode.field.QM31)
    (run : FIp_DotDecode.field.QM31.from_le_bytes bytes=ok (some out)) : FIo_QMValues.Canon out := by
  unfold FIp_DotDecode.field.QM31.from_le_bytes at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  all_goals
    have same := Option.some.inj (Result.ok.inj run)
    cases same
    constructor <;> (apply cm (branch := by assumption);assumption)

theorem source (q : Array U8 608#usize) (start stop : Usize) (out : FIp_DotDecode.field.QM31)
    (run : JFr_TX2_TailRead.read q start stop=ok out) : FIo_QMValues.Canon out := by
  unfold JFr_TX2_TailRead.read at run
  obtain ⟨s,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨o,decode,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some v =>
    have same : v=out := Result.ok.inj run
    subst out
    exact qm s v decode

#print axioms continued
#print axioms cm
#print axioms qm
#print axioms source
end AspisR1.JFs_TX2_TailQM
end
