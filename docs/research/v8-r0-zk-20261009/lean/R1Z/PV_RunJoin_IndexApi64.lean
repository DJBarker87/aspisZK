import R1Z.ProverRwFullFuns
open Aeneas.Std
namespace R1Z.PV_RunJoin_IndexApi64
def shift : Result Usize := 1#usize <<< 18#i32
set_option pp.all true in
#print shift
#print Aeneas.Std.UScalar.wrapping_shl
#print Aeneas.Std.Usize.wrapping_shl_bv_eq
end R1Z.PV_RunJoin_IndexApi64
