import NNH_Run5bCombined
import NNU_GeometryCallbacks
import NNU_GeometryInstall
import NNU_GeometryIndex
import NNU_GeometrySelected
import NNU_GeometryEnd
import NNU_GeometryBody
import NNU_GeometryStdSlots
import NNU_GeometryTraversal
import NNU_Geometry
import NNU_QueryInventory
import NNU_QueryFieldBase
import NNU_QueryFieldQM
import NNU_QueryFieldCarriers
import NNU_QueryFieldWide
import NNU_QueryLoops
import NNU_QueryAccum
import NNU_QueryValues
import NNU_QueryInduction
import NNU_QueryLoop
import NNU_Query
import NNU_MerkleSlots
import NNU_MerkleInventory
import NNU_OffsetArithmetic
import NNU_OffsetSubtract
import NNU_Offsets
import NNU_MerkleDigest
import NNU_CommonCuts
import NNU_CommonResume
import NNU_CommonSelected
import NNU_Inactive
import NNU_InactiveStructure
import NNU_MerkleChildren
import NNU_MerkleCount
import NNU_MerkleEndpoint
import NNU_MerkleEnvironment
import NNU_MerkleHead
import NNU_MerkleIteration
import NNU_MerkleKeys
import NNU_MerkleLeaf
import NNU_MerkleLevels
import NNU_MerkleNative
import NNU_MerkleNode
import NNU_MerkleOpening
import NNU_MerkleRoot
import NNU_MerkleValidity
import NNU_MerkleVerify
import NNU_MerkleWrapper
import NNU_Stage2Tail
set_option autoImplicit false
#print axioms AspisR1.NNU_Geometry.source
#print axioms AspisR1.NNU_Geometry.returned
#print axioms AspisR1.NNU_Query.source
#print axioms AspisR1.NNU_Query.returned
#print axioms AspisR1.NNU_MerkleSlots.installed
#print axioms AspisR1.NNU_MerkleSlots.same_resume
#print axioms AspisR1.NNU_MerkleDigest.node
#print axioms AspisR1.NNU_MerkleDigest.leaf
#print axioms AspisR1.NNU_Offsets.inactive
#print axioms AspisR1.NNU_Offsets.round0
#print axioms AspisR1.NNU_Offsets.folded
#print axioms AspisR1.NNU_Offsets.round1
#print axioms AspisR1.NNU_Offsets.final_offset
#print axioms AspisR1.NNU_Offsets.openings
#print axioms AspisR1.NNU_Offsets.split_value

#print axioms AspisR1.NNU_CommonCuts.source
#print axioms AspisR1.NNU_CommonResume.occurrence
#print axioms AspisR1.NNU_CommonSelected.source
#print axioms AspisR1.NNU_Inactive.source
#print axioms AspisR1.NNU_Inactive.returned
#print axioms AspisR1.NNU_InactiveStructure.post_bind
#print axioms AspisR1.NNU_InactiveStructure.post_if
#print axioms AspisR1.NNU_InactiveStructure.post_ok
#print axioms AspisR1.NNU_InactiveStructure.limbs
#print axioms AspisR1.NNU_MerkleChildren.opening
#print axioms AspisR1.NNU_MerkleChildren.key
#print axioms AspisR1.NNU_MerkleChildren.sort
#print axioms AspisR1.NNU_MerkleChildren.slot
#print axioms AspisR1.NNU_MerkleChildren.leaf
#print axioms AspisR1.NNU_MerkleCount.source
#print axioms AspisR1.NNU_MerkleEndpoint.selected
#print axioms AspisR1.NNU_MerkleEnvironment.total
#print axioms AspisR1.NNU_MerkleEnvironment.node
#print axioms AspisR1.NNU_MerkleEnvironment.sdk
#print axioms AspisR1.NNU_MerkleEnvironment.levels
#print axioms AspisR1.NNU_MerkleHead.source
#print axioms AspisR1.NNU_MerkleIteration.source
#print axioms AspisR1.NNU_MerkleKeys.source
#print axioms AspisR1.NNU_MerkleLeaf.source
#print axioms AspisR1.NNU_MerkleLevels.rows_result
#print axioms AspisR1.NNU_MerkleLevels.level_result
#print axioms AspisR1.NNU_MerkleLevels.levels_result
#print axioms AspisR1.NNU_MerkleLevels.eighteen_result
#print axioms AspisR1.NNU_MerkleNative.batch
#print axioms AspisR1.NNU_MerkleNode.writer
#print axioms AspisR1.NNU_MerkleNode.node
#print axioms AspisR1.NNU_MerkleOpening.range
#print axioms AspisR1.NNU_MerkleOpening.source
#print axioms AspisR1.NNU_MerkleRoot.final
#print axioms AspisR1.NNU_MerkleValidity.indices
#print axioms AspisR1.NNU_MerkleVerify.selected
#print axioms AspisR1.NNU_MerkleVerify.sdk
#print axioms AspisR1.NNU_MerkleWrapper.returned
#print axioms AspisR1.NNU_Stage2Tail.emitPacket
#print axioms AspisR1.NNU_Stage2Tail.tail
#print axioms AspisR1.NNU_Stage2Tail.returnedCuts
