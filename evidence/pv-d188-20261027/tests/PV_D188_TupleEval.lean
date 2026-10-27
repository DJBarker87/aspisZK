import R1Z.PV_CB_Op223TupleProducerFuns
import R1Z.PV_CB_Op223ForestProducerFuns
open Aeneas Aeneas.Std Result PV_CB_ShippedOp223Tuple
-- Concrete Rust Range::contains definition, supplied only to execute this test.
private instance : ExternalFuns where
 contains := fun _ forward backward r item => do
   let lower ← forward.le r.start item
   if lower then backward.lt item r.«end» else ok false
private def cells (v : pool_v1.pair_trace.PoolV1PairCopyTupleV1) : List (List Nat) :=
 v.limbs.val.map fun l => match l with
 | .Zero => []
 | .Cell s o => [s.cell.row.val,s.cell.column.val,o.val,match s.bank with | .Stable => 0 | .Late => 1]
#eval (do let v ← pool_v1.pair_trace.tuple_cells 550#usize 3#usize 3#usize true
          ok (cells v) : Result (List (List Nat)))
#eval (do let v ← PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells 550#usize 3#usize 3#usize true
          ok (cells v) : Result (List (List Nat)))
