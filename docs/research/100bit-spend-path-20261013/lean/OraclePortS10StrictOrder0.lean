import OraclePortS10StrictOrder
import OraclePortS10Dominance0

/-! Earlier block occurrence on every path reaching the selected later call.
Exact graph/source coordinates are retained in strict-order-map.json. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10StrictOrder0
open OraclePortS10CFG OraclePortS10StrictOrder

theorem fact_0 {visits : List Nat}
    (path : Path OraclePortS10Dominance0.Edge 0 8 visits) :
    BeforeEnd 0 8 visits :=
  before_end OraclePortS10Dominance0.fact_0 (by omega) path

#print axioms fact_0

theorem fact_1 {visits : List Nat}
    (path : Path OraclePortS10Dominance0.Edge 0 10 visits) :
    BeforeEnd 0 10 visits :=
  before_end OraclePortS10Dominance0.fact_1 (by omega) path

#print axioms fact_1

theorem fact_2 {visits : List Nat}
    (path : Path OraclePortS10Dominance0.Edge 0 10 visits) :
    BeforeEnd 8 10 visits :=
  before_end OraclePortS10Dominance0.fact_2 (by omega) path

#print axioms fact_2
end AspisR1.OraclePortS10StrictOrder0
