import PV_B3P_PrefixEmission224
import PV_B3P_HelperMut224
namespace PV_B3P_HelperSide224
open Aeneas Aeneas.Std PV_B3P_224Prefix
set_option autoImplicit false

-- This law exposes both restored arrays and the final outer-array write.
-- Arithmetic remains symbolic, including its failure behavior outside the
-- explicitly stated successful tuple/compression branch.
theorem producer_zero (rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize)
    (view : prefix224.View) (tuple : aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1)
    (tag weight : aspis_core.field.M31) (lambda value : aspis_core.field.QM31)
    (row : aspis_statement.logup.CopyLogUpRow) (values : Array aspis_core.field.M31 16#usize)
    (hr : (UScalar.cast .Usize tuple.row).val < 1024)
    (hrow : prefix224.row_at rows (UScalar.cast .Usize tuple.row) = .ok row)
    (hz : PV_B3P_HelperIndex224.zero row.producer_weights = aspis_core.field.M31.ZERO)
    (ht : prefix224.tuple_value view tuple = .ok values)
    (hc : prefix224.compress tag values lambda = .ok value) :
    prefix224.side rows view tuple tag weight lambda false =
      .ok (.Ok (rows.set (UScalar.cast .Usize tuple.row)
        {row with producer_values := row.producer_values.set 0#usize value
                  producer_weights := row.producer_weights.set 0#usize weight})) := by
  let output : aspis_statement.logup.CopyLogUpRow :=
    {row with producer_values := row.producer_values.set 0#usize value
              producer_weights := row.producer_weights.set 0#usize weight}
  obtain ⟨out,hout,hval⟩ := WP.spec_imp_exists (Array.update_spec rows (UScalar.cast .Usize tuple.row) output (by
    have h := rows.property; scalar_tac))
  simp [prefix224.side,lift,hrow,PV_B3P_HelperIndex224.index_zero,hz,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,ht,hc,PV_B3P_HelperMut224.zero,output,hout,hval]

#print axioms producer_zero
end PV_B3P_HelperSide224
