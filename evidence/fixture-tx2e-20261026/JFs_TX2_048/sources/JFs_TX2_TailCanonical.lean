import JFr_TX2_TailRead
import FIo_QMValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_TailCanonical
open Aeneas Aeneas.Std Result

theorem scalar {bytes : Array U8 4#usize} {o : Option U32} {v : U32}
    (decode : FIp_DotDecode.field.M31.from_le_bytes bytes=ok o)
    (branch : FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitTry.branch o=
      ok (core.ops.control_flow.ControlFlow.Continue v)) : v.val<2147483647 := by
  cases o with
  | none => simp only [FIp_DotDecode.core.option.Option.Insts.CoreOpsTry_traitTry.branch] at branch;cases branch
  | some a =>
    have same : a=v := by exact core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj branch)
    subst a
    unfold FIp_DotDecode.field.M31.from_le_bytes at decode
    simp only [lift,bind_tc_ok,FIp_DotDecode.field.P] at decode
    split at decode
    · cases decode
    · rename_i h
      have same := Option.some.inj (Result.ok.inj decode)
      subst v
      scalar_tac

theorem cm (bytes : Slice U8) (out : FIp_DotDecode.field.CM31)
    (run : FIp_DotDecode.field.CM31.from_le_bytes bytes=ok (some out)) : FIo_CMValues.Canon out := by
  unfold FIp_DotDecode.field.CM31.from_le_bytes FIp_DotDecode.field.M31.from_le_bytes at run
  simp only [FIp_DotDecode.field.P,lift,bind_tc_ok] at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  all_goals
    have same := Option.some.inj (Result.ok.inj run)
    cases same
    constructor <;> (apply scalar <;> assumption)

#print axioms scalar
#print axioms cm
end AspisR1.JFs_TX2_TailCanonical
end
