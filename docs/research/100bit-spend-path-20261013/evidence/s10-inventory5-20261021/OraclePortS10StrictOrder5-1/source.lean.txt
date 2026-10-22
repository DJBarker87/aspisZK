import OraclePortS10StrictOrder
import OraclePortS10Dominance5

/-! Earlier block occurrence on every path reaching the selected later call.
Exact graph/source coordinates are retained in strict-order-map.json. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10StrictOrder5
open OraclePortS10CFG OraclePortS10StrictOrder

theorem fact_0 {visits : List Nat}
    (path : Path OraclePortS10Dominance5.Edge 0 2 visits) :
    BeforeEnd 0 2 visits :=
  before_end OraclePortS10Dominance5.fact_0 (by omega) path

#print axioms fact_0
end AspisR1.OraclePortS10StrictOrder5
