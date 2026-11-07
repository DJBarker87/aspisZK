import NNK_COMBINED_IMPORT
example (allocations : RSL.TX2_234.Args → RSL.Env → Nat → Bool) :
 RSL.TX2_234.RowSpec_234 LIBB_PoolLib.library LIBB_PoolLib.deployed (NMX_R3_RegistryRoot.authenticate allocations) := NMX_R3_RegistryRoot.root allocations
example (allocationSucceeded : RSL.Bytes → RSL.Env → Bool) :
 RSL.TX2_217.RowSpec_217 (NMX_R3_DecoderFold.decode allocationSucceeded) := NMX_R3_DecoderFold.root allocationSucceeded
#print RSL.TX2_234.RowSpec_234
#print NMX_R3_RegistryRoot.root
#print NMX_R3_RegistryRoot.authenticate
#print NMX_R3_RegistryProjectionRef.reference
#print NMX_R3_RegistryNativeFold.native
#print NMX_R3_RegistryIds.pool
#print NMX_R3_RegistryIds.registry
#print RSL.TX2_217.RowSpec_217
#print NMX_R3_DecoderFold.root
#print NMX_R3_DecoderFold.complete
#print axioms NMX_R3_RegistryRoot.root
#print axioms NMX_R3_DecoderFold.root
example (a : RSL.TX2_234.Args) : RSL.TX2_234.Domain a = True := rfl
example (bytes : RSL.Bytes) : RSL.TX2_217.Domain bytes = True := rfl
#print axioms RSL.TX2_234.rejects_constAbort
