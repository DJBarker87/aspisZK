import OraclePortS10StrictOrder
import OraclePortS10Dominance4

/-! Earlier block occurrence on every path reaching the selected later call.
Exact graph/source coordinates are retained in strict-order-map.json. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10StrictOrder4
open OraclePortS10CFG OraclePortS10StrictOrder

theorem fact_0 {visits : List Nat}
    (path : Path OraclePortS10Dominance4.Edge 0 4 visits) :
    BeforeEnd 0 4 visits :=
  before_end OraclePortS10Dominance4.fact_0 (by omega) path

#print axioms fact_0

theorem fact_1 {visits : List Nat}
    (path : Path OraclePortS10Dominance4.Edge 0 7 visits) :
    BeforeEnd 0 7 visits :=
  before_end OraclePortS10Dominance4.fact_1 (by omega) path

#print axioms fact_1

theorem fact_2 {visits : List Nat}
    (path : Path OraclePortS10Dominance4.Edge 0 4 visits) :
    BeforeEnd 7 4 visits :=
  before_end OraclePortS10Dominance4.fact_2 (by omega) path

#print axioms fact_2
end AspisR1.OraclePortS10StrictOrder4
