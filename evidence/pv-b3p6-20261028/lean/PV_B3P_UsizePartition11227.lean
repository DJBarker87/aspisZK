import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
theorem usize_partition11 : ([[0#usize, 1#usize, 2#usize, 3#usize], [4#usize, 5#usize, 6#usize, 7#usize], [8#usize, 9#usize, 10#usize, 11#usize], [12#usize, 13#usize, 14#usize, 15#usize]] : List (List Usize)).flatten = [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] := by
  rfl
#print axioms usize_partition11
end PV_B3P_Binding11227
