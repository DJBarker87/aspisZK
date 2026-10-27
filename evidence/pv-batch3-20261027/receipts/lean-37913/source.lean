import PV_B3_PrefixRank222
import PV_B3_BoundedLoop
namespace PV_B3_PrefixFinite222
open Aeneas Aeneas.Std Result PV_B3_Copy_222 PV_B3_PrefixCounter222
set_option autoImplicit false

theorem source (point : Array Q 10#usize) :
    host_multilinear.sparse_eq_weights_loop0 point 10#usize =
      PV_B3_BoundedLoop.bounded (host_multilinear.sparse_eq_weights_loop0.body point)
        10 10#usize := by
  exact PV_B3_BoundedLoop.source_eq_bounded
    (host_multilinear.sparse_eq_weights_loop0.body point) (fun i => i.val)
    (PV_B3_PrefixRank222.decreases point) 10 10#usize (by decide)

#print axioms source
end PV_B3_PrefixFinite222
