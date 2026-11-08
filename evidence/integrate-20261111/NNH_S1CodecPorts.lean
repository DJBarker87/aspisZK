import NNH_HostExec
import NNH_S1CodecOk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_S1CodecPorts
open Aeneas Aeneas.Std Result
#print AspisS6CurrentCodecInstallation.install
#print NMT_345.validateCall
#print NMT_345.encodeCall
#print NMT_345.commonValue
#print AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1
end AspisR1.NNH_S1CodecPorts
end
#check AdapterRw.Ops.op21
#check AdapterRw.Ops.op24
open Lean in
run_cmd do
 let env ← getEnv
 for (n,info) in env.constants.toList do
  let s := n.toString
  if s.startsWith "AspisS6CurrentAdapterCarrier.toPoolV1" && !s.contains "._" && !s.contains ".eq_" then
   logInfo m!"{n}: {info.type}"
#check NMT_345Dec.fromT5
