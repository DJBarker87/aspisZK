import Aeneas
import AspisR1CanonicalQRawUnified.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
#print Aeneas.Std.core.array.Array.map
#check @Aeneas.Std.core.array.Array.map_success
#print Aeneas.Std.Array.index_usize
#print core.convert.num.FromU64U32.from
#print Aeneas.Std.lift
#print AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut
#print AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call
#check @AspisV8R19.TraversalRuntime.mapState
#print Aeneas.Std.Array.make
#check @Aeneas.Std.bind_tc_ok
#check @bind_assoc
-- shift lemma probes
example (x : U64) : (x >>> 31#i32) = (x >>> 31#u32) := by first | rfl | (simp [HShiftRight.hShiftRight]; done)
example (x : U64) : (x >>> 31#i32) = (x >>> 31#u32) := by
  unfold HShiftRight.hShiftRight instHShiftRight_aeneas
  rfl
-- index on literal array
example (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = ok a := by first | rfl | simp [Array.make, Array.index_usize]
example (a b c d : U64) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = ok d := by first | rfl | simp [Array.make, Array.index_usize]
