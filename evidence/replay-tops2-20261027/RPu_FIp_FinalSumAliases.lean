import RPu_FIp_FinalSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_FinalSumAliases
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem six (iter : FIo_RangeNext.Range) (p k : Array NE 7#usize) (s : NE) :
    FIo_Native.weights.Weights.pair_loop6 iter p k s=FIo_Native.weights.Weights.pair_loop17 iter p k s := rfl

theorem nine (iter : FIo_RangeNext.Range) (p k : Array NE 7#usize) (s : NE) :
    FIo_Native.weights.Weights.pair_loop9 iter p k s=FIo_Native.weights.Weights.pair_loop17 iter p k s := rfl

theorem fourteen (iter : FIo_RangeNext.Range) (p k : Array NE 7#usize) (s : NE) :
    FIo_Native.weights.Weights.pair_loop14 iter p k s=FIo_Native.weights.Weights.pair_loop17 iter p k s := rfl

#print axioms six
#print axioms nine
#print axioms fourteen
end AspisR1.FIp_FinalSumAliases
end
