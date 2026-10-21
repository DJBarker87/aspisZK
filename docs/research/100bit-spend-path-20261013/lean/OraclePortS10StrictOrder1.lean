import OraclePortS10StrictOrder
import OraclePortS10Dominance1

/-! Earlier block occurrence on every path reaching the selected later call.
Exact graph/source coordinates are retained in strict-order-map.json. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10StrictOrder1
open OraclePortS10CFG OraclePortS10StrictOrder

theorem fact_0 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 5 visits) :
    BeforeEnd 2 5 visits :=
  before_end OraclePortS10Dominance1.fact_0 (by omega) path

#print axioms fact_0

theorem fact_1 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 10 visits) :
    BeforeEnd 2 10 visits :=
  before_end OraclePortS10Dominance1.fact_1 (by omega) path

#print axioms fact_1

theorem fact_2 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 12 visits) :
    BeforeEnd 2 12 visits :=
  before_end OraclePortS10Dominance1.fact_2 (by omega) path

#print axioms fact_2

theorem fact_3 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 21 visits) :
    BeforeEnd 2 21 visits :=
  before_end OraclePortS10Dominance1.fact_3 (by omega) path

#print axioms fact_3

theorem fact_4 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 23 visits) :
    BeforeEnd 2 23 visits :=
  before_end OraclePortS10Dominance1.fact_4 (by omega) path

#print axioms fact_4

theorem fact_5 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 28 visits) :
    BeforeEnd 2 28 visits :=
  before_end OraclePortS10Dominance1.fact_5 (by omega) path

#print axioms fact_5

theorem fact_6 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 30 visits) :
    BeforeEnd 2 30 visits :=
  before_end OraclePortS10Dominance1.fact_6 (by omega) path

#print axioms fact_6

theorem fact_7 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 61 visits) :
    BeforeEnd 2 61 visits :=
  before_end OraclePortS10Dominance1.fact_7 (by omega) path

#print axioms fact_7

theorem fact_8 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 75 visits) :
    BeforeEnd 2 75 visits :=
  before_end OraclePortS10Dominance1.fact_8 (by omega) path

#print axioms fact_8

theorem fact_9 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 10 visits) :
    BeforeEnd 5 10 visits :=
  before_end OraclePortS10Dominance1.fact_9 (by omega) path

#print axioms fact_9

theorem fact_10 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 12 visits) :
    BeforeEnd 5 12 visits :=
  before_end OraclePortS10Dominance1.fact_10 (by omega) path

#print axioms fact_10

theorem fact_11 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 21 visits) :
    BeforeEnd 5 21 visits :=
  before_end OraclePortS10Dominance1.fact_11 (by omega) path

#print axioms fact_11

theorem fact_12 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 23 visits) :
    BeforeEnd 5 23 visits :=
  before_end OraclePortS10Dominance1.fact_12 (by omega) path

#print axioms fact_12

theorem fact_13 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 28 visits) :
    BeforeEnd 5 28 visits :=
  before_end OraclePortS10Dominance1.fact_13 (by omega) path

#print axioms fact_13

theorem fact_14 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 30 visits) :
    BeforeEnd 5 30 visits :=
  before_end OraclePortS10Dominance1.fact_14 (by omega) path

#print axioms fact_14

theorem fact_15 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 61 visits) :
    BeforeEnd 5 61 visits :=
  before_end OraclePortS10Dominance1.fact_15 (by omega) path

#print axioms fact_15

theorem fact_16 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 75 visits) :
    BeforeEnd 5 75 visits :=
  before_end OraclePortS10Dominance1.fact_16 (by omega) path

#print axioms fact_16

theorem fact_17 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 12 visits) :
    BeforeEnd 10 12 visits :=
  before_end OraclePortS10Dominance1.fact_17 (by omega) path

#print axioms fact_17

theorem fact_18 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 21 visits) :
    BeforeEnd 10 21 visits :=
  before_end OraclePortS10Dominance1.fact_18 (by omega) path

#print axioms fact_18

theorem fact_19 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 23 visits) :
    BeforeEnd 10 23 visits :=
  before_end OraclePortS10Dominance1.fact_19 (by omega) path

#print axioms fact_19

theorem fact_20 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 28 visits) :
    BeforeEnd 10 28 visits :=
  before_end OraclePortS10Dominance1.fact_20 (by omega) path

#print axioms fact_20

theorem fact_21 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 30 visits) :
    BeforeEnd 10 30 visits :=
  before_end OraclePortS10Dominance1.fact_21 (by omega) path

#print axioms fact_21

theorem fact_22 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 61 visits) :
    BeforeEnd 10 61 visits :=
  before_end OraclePortS10Dominance1.fact_22 (by omega) path

#print axioms fact_22

theorem fact_23 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 75 visits) :
    BeforeEnd 10 75 visits :=
  before_end OraclePortS10Dominance1.fact_23 (by omega) path

#print axioms fact_23

theorem fact_24 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 21 visits) :
    BeforeEnd 12 21 visits :=
  before_end OraclePortS10Dominance1.fact_24 (by omega) path

#print axioms fact_24

theorem fact_25 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 23 visits) :
    BeforeEnd 12 23 visits :=
  before_end OraclePortS10Dominance1.fact_25 (by omega) path

#print axioms fact_25

theorem fact_26 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 28 visits) :
    BeforeEnd 12 28 visits :=
  before_end OraclePortS10Dominance1.fact_26 (by omega) path

#print axioms fact_26

theorem fact_27 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 30 visits) :
    BeforeEnd 12 30 visits :=
  before_end OraclePortS10Dominance1.fact_27 (by omega) path

#print axioms fact_27

theorem fact_28 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 61 visits) :
    BeforeEnd 12 61 visits :=
  before_end OraclePortS10Dominance1.fact_28 (by omega) path

#print axioms fact_28

theorem fact_29 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 75 visits) :
    BeforeEnd 12 75 visits :=
  before_end OraclePortS10Dominance1.fact_29 (by omega) path

#print axioms fact_29

theorem fact_30 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 23 visits) :
    BeforeEnd 21 23 visits :=
  before_end OraclePortS10Dominance1.fact_30 (by omega) path

#print axioms fact_30

theorem fact_31 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 28 visits) :
    BeforeEnd 21 28 visits :=
  before_end OraclePortS10Dominance1.fact_31 (by omega) path

#print axioms fact_31

theorem fact_32 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 30 visits) :
    BeforeEnd 21 30 visits :=
  before_end OraclePortS10Dominance1.fact_32 (by omega) path

#print axioms fact_32

theorem fact_33 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 75 visits) :
    BeforeEnd 21 75 visits :=
  before_end OraclePortS10Dominance1.fact_33 (by omega) path

#print axioms fact_33

theorem fact_34 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 28 visits) :
    BeforeEnd 23 28 visits :=
  before_end OraclePortS10Dominance1.fact_34 (by omega) path

#print axioms fact_34

theorem fact_35 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 30 visits) :
    BeforeEnd 23 30 visits :=
  before_end OraclePortS10Dominance1.fact_35 (by omega) path

#print axioms fact_35

theorem fact_36 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 75 visits) :
    BeforeEnd 23 75 visits :=
  before_end OraclePortS10Dominance1.fact_36 (by omega) path

#print axioms fact_36

theorem fact_37 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 30 visits) :
    BeforeEnd 28 30 visits :=
  before_end OraclePortS10Dominance1.fact_37 (by omega) path

#print axioms fact_37

theorem fact_38 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 21 visits) :
    BeforeEnd 61 21 visits :=
  before_end OraclePortS10Dominance1.fact_38 (by omega) path

#print axioms fact_38

theorem fact_39 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 23 visits) :
    BeforeEnd 61 23 visits :=
  before_end OraclePortS10Dominance1.fact_39 (by omega) path

#print axioms fact_39

theorem fact_40 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 28 visits) :
    BeforeEnd 61 28 visits :=
  before_end OraclePortS10Dominance1.fact_40 (by omega) path

#print axioms fact_40

theorem fact_41 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 30 visits) :
    BeforeEnd 61 30 visits :=
  before_end OraclePortS10Dominance1.fact_41 (by omega) path

#print axioms fact_41

theorem fact_42 {visits : List Nat}
    (path : Path OraclePortS10Dominance1.Edge 0 75 visits) :
    BeforeEnd 61 75 visits :=
  before_end OraclePortS10Dominance1.fact_42 (by omega) path

#print axioms fact_42
end AspisR1.OraclePortS10StrictOrder1
