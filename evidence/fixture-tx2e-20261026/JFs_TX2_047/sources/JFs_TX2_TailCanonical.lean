import JFr_TX2_TailRead
import FIo_QMValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_TailCanonical
open Aeneas Aeneas.Std Result

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
    constructor <;> scalar_tac

#print axioms cm
end AspisR1.JFs_TX2_TailCanonical
end
