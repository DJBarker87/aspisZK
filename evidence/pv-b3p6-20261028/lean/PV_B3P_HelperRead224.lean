import PV_B3P_Emission224
namespace PV_B3P_HelperRead224
open Aeneas Aeneas.Std PV_B3P_224
set_option autoImplicit false

def rowValue (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (r : Usize) (hr : r.val < 1024) : aspis_statement.logup.CopyLogUpRow :=
  rows.val[r.val]'(by have h := rows.property; scalar_tac)

theorem source (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (r : Usize) (hr : r.val < 1024) : reference224.row_at rows r = .ok (rowValue rows r hr) := by
  obtain ⟨row,hrow,hval⟩ := WP.spec_imp_exists (Array.index_usize_spec rows r (by
    have h := rows.property; scalar_tac))
  simpa only [reference224.row_at,rowValue,hval] using hrow

#print axioms source
end PV_B3P_HelperRead224
