import LIBB_PoolEffects
import LIBB_PoolDecoders
import LIBB_PoolRegistry
import LIBB_PoolAccounts
import LIB_Deployed
import NND_PoolValues
set_option autoImplicit false
noncomputable section
namespace LIBB_PoolLib
/-- One concrete library shared by every TX2 principal and returned-value
consumer. All fields are fixed CLOSED-model values; no Ops or child parameter. -/
def library : RSL.PoolLib where
 Request := LIBB_PoolCarriers.Request
 Statement := LIBB_PoolCarriers.Statement
 Afterstate := LIBB_PoolCarriers.Afterstate
 decodeRequest := LIBB_PoolDecoders.decodeRequest
 reqProfile := LIBB_PoolDecoders.reqProfile
 reqRelease := LIBB_PoolDecoders.reqRelease
 reqPoolProgram := LIBB_PoolDecoders.reqPoolProgram
 reqNullifier := LIBB_PoolDecoders.reqNullifier
 outputLane := LIBB_PoolDecoders.outputLane
 decodeMaster := LIBB_PoolAccounts.decodeMaster
 decodeCheckpoint := LIBB_PoolAccounts.decodeCheckpoint
 validatePolicy := LIBB_PoolRegistry.validatePolicy
 decodeRegistryV1 := LIBB_PoolRegistry.decodeRegistryV1
 decodeRegistryV2 := LIBB_PoolRegistry.decodeRegistryV2
 decodeEntryV1 := LIBB_PoolRegistry.decodeEntryV1
 decodeEntryV2 := LIBB_PoolRegistry.decodeEntryV2
 scanProof := LIBB_PoolEffects.scanProof
 reconstruct := LIBB_PoolEffects.reconstruct
 encodeStatement := LIBB_PoolEffects.encodeStatement
 emitResult := LIBB_PoolEffects.emitResult
abbrev deployed := LIB_Deployed.deployed
/-- Every returned evaluator is instantiated. Aborted executions carry no
invented reply and are handled vacuously only by Returns' stated definition. -/
def values : NND_PoolValues.Values library where
 scan := fun data _ => LIBB_PoolScan.evaluator data
 reconstruct := fun q a c _ => LIBB_PoolReconstruct.evaluator q a c
 encode := fun s _ => LIBB_PoolEncode.evaluator s
 emit := fun s _ => LIBB_PoolEmit.evaluator s
 scan_ret := LIBB_PoolScan.returns
 reconstruct_ret := LIBB_PoolReconstruct.returns
 encode_ret := LIBB_PoolEncode.returns
 emit_ret := LIBB_PoolEmit.returns

theorem scanner_extent : NMS_R2Facts242.ScannerExtent library := LIBB_ScannerExtent.extent

theorem carrier_identity :
 library.Request = LIBB_PoolCarriers.Request ∧
 library.Statement = LIBB_PoolCarriers.Statement ∧
 library.Afterstate = LIBB_PoolCarriers.Afterstate := ⟨rfl,rfl,rfl⟩
#print axioms values
#print axioms scanner_extent
#print axioms carrier_identity
end LIBB_PoolLib
end
