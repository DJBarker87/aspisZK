import NNH_Tx2ConcreteInputs
import NNH_CommonResumeDomain
open Aeneas Aeneas.Std AspisR1
#check Slice.index_range_spec
#check Slice.index_range
#check Slice.get_range_spec
#check Slice.index_range_to_spec
#print Port4A_ReaderInstall.reader
#print NJC_FilledClause.reserved
#print RSL.TX2_241.Dom064
#print NND_Carrier.bytes
#print NNH_SmallUsize.mul
open Lean in
run_cmd do
 let env ← getEnv
 for (n,_) in env.constants.toList do
  if n.toString.startsWith "Aeneas.Std.Slice." && ((n.toString.splitOn "range").length>1 || (n.toString.splitOn "Range").length>1) then logInfo m!"{n}"
