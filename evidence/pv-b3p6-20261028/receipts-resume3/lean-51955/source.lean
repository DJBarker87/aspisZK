import PV_B3P_HelperRead224
namespace PV_B3P_HelperAbort224
open Aeneas Aeneas.Std PV_B3P_224
set_option autoImplicit false

theorem failure (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (out : Array aspis_core.field.QM31 1024#usize)
    (r : Usize) (hr : r.val < 1024) (e : Aeneas.Std.Error)
    (heval : reference224.one_row (PV_B3P_HelperRead224.rowValue rows r hr) chi = .fail e) :
    reference224.from_rows_loop.body rows chi out r = .fail e := by
  have hb : r < 1024#usize := by scalar_tac
  simp only [reference224.from_rows_loop.body,hb,↓reduceIte,PV_B3P_HelperRead224.source rows r hr,
    heval,bind_tc_ok,bind_tc_fail]

theorem divergence (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (chi : aspis_core.field.QM31) (out : Array aspis_core.field.QM31 1024#usize)
    (r : Usize) (hr : r.val < 1024)
    (heval : reference224.one_row (PV_B3P_HelperRead224.rowValue rows r hr) chi = .div) :
    reference224.from_rows_loop.body rows chi out r = .div := by
  have hb : r < 1024#usize := by scalar_tac
  simp only [reference224.from_rows_loop.body,hb,↓reduceIte,PV_B3P_HelperRead224.source rows r hr,
    heval,bind_tc_ok,bind_tc_div]

#print axioms failure
#print axioms divergence
end PV_B3P_HelperAbort224
