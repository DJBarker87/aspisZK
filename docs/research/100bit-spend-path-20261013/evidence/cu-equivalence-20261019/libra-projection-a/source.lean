import CuSavingsLibraSourceHandback
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourceProjection
open Aeneas Aeneas.Std Result AspisR1Libra
variable [Shared]

theorem power_once_projection (N : Usize) (c : kpowers.closure N) (i : Usize) :
    (kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31 N).call_once c i =
      (do let (value,_) ← kpowers.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once c i
          .ok value) := rfl

theorem reference_once_instance_projection (c : old.twofold_libra_weights.closure.closure) (i : Usize) :
    (old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31).call_once c i =
      (do let (value,_) ←
        old.twofold_libra_weights.closure.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once c i
          .ok value) := rfl

#print axioms power_once_projection
#print axioms reference_once_instance_projection
end AspisR1.CuSavingsLibraSourceProjection
