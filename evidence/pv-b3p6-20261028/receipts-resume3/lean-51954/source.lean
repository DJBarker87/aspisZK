import PV_B3P_HelperRead224
namespace PV_B3P_HelperStep224
open Aeneas Aeneas.Std PV_B3P_224
set_option autoImplicit false

theorem success (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (out : Array aspis_core.field.QM31 1024#usize)
    (r : Usize) (hr : r.val < 1024) (value : aspis_core.field.QM31)
    (heval : reference224.one_row (PV_B3P_HelperRead224.rowValue rows r hr) chi = .ok (.Ok value)) :
    reference224.from_rows_loop.body rows chi out r =
      .ok (.cont (out.set r value,Usize.wrapping_add r 1#usize)) := by
  have hb : r < 1024#usize := by scalar_tac
  obtain ⟨out',hout',hval⟩ := WP.spec_imp_exists (Array.update_spec out r value (by
    have h := out.property; scalar_tac))
  simp only [reference224.from_rows_loop.body,hb,↓reduceIte,PV_B3P_HelperRead224.source rows r hr,
    heval,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,hout',hval,lift]

theorem rejection (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (out : Array aspis_core.field.QM31 1024#usize)
    (r : Usize) (hr : r.val < 1024) (e : reference224.Error)
    (heval : reference224.one_row (PV_B3P_HelperRead224.rowValue rows r hr) chi = .ok (.Err e)) :
    reference224.from_rows_loop.body rows chi out r = .ok (.done (out,some (.Err e))) := by
  have hb : r < 1024#usize := by scalar_tac
  simp only [reference224.from_rows_loop.body,hb,↓reduceIte,PV_B3P_HelperRead224.source rows r hr,
    heval,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame]

theorem stopped (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (out : Array aspis_core.field.QM31 1024#usize)
    (r : Usize) (hr : 1024 ≤ r.val) :
    reference224.from_rows_loop.body rows chi out r = .ok (.done (out,none)) := by
  have hb : ¬ r < 1024#usize := by scalar_tac
  simp only [reference224.from_rows_loop.body,hb,↓reduceIte]

#print axioms success
#print axioms rejection
#print axioms stopped
end PV_B3P_HelperStep224
