import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

theorem sixteen_group_finish10 {α β : Type} (step : α → Usize → Result α)
    (initial : α) (finish : α → Result β) :
    (do
      let s0 ← PV_B3P_Ordered227.fold step [0#usize, 1#usize, 2#usize, 3#usize] initial
      let s1 ← PV_B3P_Ordered227.fold step [4#usize, 5#usize, 6#usize, 7#usize] s0
      let s2 ← PV_B3P_Ordered227.fold step [8#usize, 9#usize, 10#usize, 11#usize] s1
      let s3 ← PV_B3P_Ordered227.fold step [12#usize, 13#usize, 14#usize, 15#usize] s2
      finish s3) = (do
      let next ← PV_B3P_Ordered227.fold step [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] initial
      finish next) := by
  have h := PV_B3P_Ordered227.flatten step [[0#usize, 1#usize, 2#usize, 3#usize], [4#usize, 5#usize, 6#usize, 7#usize], [8#usize, 9#usize, 10#usize, 11#usize], [12#usize, 13#usize, 14#usize, 15#usize]] initial
  have joined := congrArg (fun result => result >>= finish) h
  simpa only [PV_B3P_Ordered227.ranges,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using joined
#print axioms sixteen_group_finish10
end PV_B3P_Binding10227
