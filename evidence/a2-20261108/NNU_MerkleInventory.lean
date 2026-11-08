import NNU_MerkleSlots
import NNH_NativeOracleReply
import Lean
set_option autoImplicit false
#print LIBB_PartitionEnv.digest
#print LIBB_PartitionEnv.H
#check LIBB_PartitionEnv.partition_value
#check LIBB_FlattenBytes.node
#check LIBB_C04InputPartition.input
#print NJS_RuntimeDigest.backend
#print NJS_BatchLeaf.modelDigest
run_cmd do
 let env ← Lean.getEnv
 for (n,i) in env.constants.toList do
  let s:=n.toString
  if i.isTheorem && ((s.startsWith "AspisR1.MultiproofCone" &&
   (s.contains "verify" || s.contains "eval")) ||
   (s.startsWith "NJS_" && (s.contains "source" || s.contains "digest"))) then
   Lean.logInfo m!"{n}: {i.type}"
