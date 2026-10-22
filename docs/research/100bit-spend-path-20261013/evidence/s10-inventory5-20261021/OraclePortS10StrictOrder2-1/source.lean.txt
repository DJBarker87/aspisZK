import OraclePortS10StrictOrder
import OraclePortS10Dominance2

/-! Earlier block occurrence on every path reaching the selected later call.
Exact graph/source coordinates are retained in strict-order-map.json. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10StrictOrder2
open OraclePortS10CFG OraclePortS10StrictOrder

theorem fact_0 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 12 visits) :
    BeforeEnd 0 12 visits :=
  before_end OraclePortS10Dominance2.fact_0 (by omega) path

#print axioms fact_0

theorem fact_1 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 14 visits) :
    BeforeEnd 0 14 visits :=
  before_end OraclePortS10Dominance2.fact_1 (by omega) path

#print axioms fact_1

theorem fact_2 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 19 visits) :
    BeforeEnd 0 19 visits :=
  before_end OraclePortS10Dominance2.fact_2 (by omega) path

#print axioms fact_2

theorem fact_3 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 50 visits) :
    BeforeEnd 0 50 visits :=
  before_end OraclePortS10Dominance2.fact_3 (by omega) path

#print axioms fact_3

theorem fact_4 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 64 visits) :
    BeforeEnd 0 64 visits :=
  before_end OraclePortS10Dominance2.fact_4 (by omega) path

#print axioms fact_4

theorem fact_5 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 74 visits) :
    BeforeEnd 0 74 visits :=
  before_end OraclePortS10Dominance2.fact_5 (by omega) path

#print axioms fact_5

theorem fact_6 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 14 visits) :
    BeforeEnd 12 14 visits :=
  before_end OraclePortS10Dominance2.fact_6 (by omega) path

#print axioms fact_6

theorem fact_7 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 19 visits) :
    BeforeEnd 12 19 visits :=
  before_end OraclePortS10Dominance2.fact_7 (by omega) path

#print axioms fact_7

theorem fact_8 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 64 visits) :
    BeforeEnd 12 64 visits :=
  before_end OraclePortS10Dominance2.fact_8 (by omega) path

#print axioms fact_8

theorem fact_9 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 74 visits) :
    BeforeEnd 12 74 visits :=
  before_end OraclePortS10Dominance2.fact_9 (by omega) path

#print axioms fact_9

theorem fact_10 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 19 visits) :
    BeforeEnd 14 19 visits :=
  before_end OraclePortS10Dominance2.fact_10 (by omega) path

#print axioms fact_10

theorem fact_11 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 64 visits) :
    BeforeEnd 14 64 visits :=
  before_end OraclePortS10Dominance2.fact_11 (by omega) path

#print axioms fact_11

theorem fact_12 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 74 visits) :
    BeforeEnd 14 74 visits :=
  before_end OraclePortS10Dominance2.fact_12 (by omega) path

#print axioms fact_12

theorem fact_13 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 74 visits) :
    BeforeEnd 19 74 visits :=
  before_end OraclePortS10Dominance2.fact_13 (by omega) path

#print axioms fact_13

theorem fact_14 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 12 visits) :
    BeforeEnd 50 12 visits :=
  before_end OraclePortS10Dominance2.fact_14 (by omega) path

#print axioms fact_14

theorem fact_15 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 14 visits) :
    BeforeEnd 50 14 visits :=
  before_end OraclePortS10Dominance2.fact_15 (by omega) path

#print axioms fact_15

theorem fact_16 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 19 visits) :
    BeforeEnd 50 19 visits :=
  before_end OraclePortS10Dominance2.fact_16 (by omega) path

#print axioms fact_16

theorem fact_17 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 64 visits) :
    BeforeEnd 50 64 visits :=
  before_end OraclePortS10Dominance2.fact_17 (by omega) path

#print axioms fact_17

theorem fact_18 {visits : List Nat}
    (path : Path OraclePortS10Dominance2.Edge 0 74 visits) :
    BeforeEnd 50 74 visits :=
  before_end OraclePortS10Dominance2.fact_18 (by omega) path

#print axioms fact_18
end AspisR1.OraclePortS10StrictOrder2
