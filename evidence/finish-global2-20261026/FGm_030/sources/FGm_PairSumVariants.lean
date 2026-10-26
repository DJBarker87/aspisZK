import FGm_PairSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_PairSumVariants
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem shared_one : FIo_Native.weights.Weights.pair_loop6=FIo_Native.weights.Weights.pair_loop9 := rfl
theorem separate_one : FIo_Native.weights.Weights.pair_loop14=FIo_Native.weights.Weights.pair_loop9 := rfl
theorem separate_two : FIo_Native.weights.Weights.pair_loop17=FIo_Native.weights.Weights.pair_loop9 := rfl

#print axioms shared_one
#print axioms separate_one
#print axioms separate_two
end AspisR1.FGm_PairSumVariants
end
