import Lean
import R1MerkleProgram
import R1CanonicalMerkleProgram
import R1CanonicalMerkleCollision
import R1CanonicalReadCollision
import R1ParsedTargetsFirstHit
import R1ParsedTargetsPrefixHit
import R1CanonicalMerkleRecovery
import R1CanonicalPredictedRecovery
import R1CanonicalFullTraceRecovery
import R1CommitmentRootFrames
import R1ThreeCommitmentFullTrace
import R1TraceTableMembership
import R1CanonicalLogMembership
import R1CanonicalLogSeparation
import R1MerkleNodeLookupExt
import R1MerkleNodeRecordUnique
import R1MerkleLeafLookupExt
import R1MerkleLeafRecordUnique
import R1MerkleLogExt
import R1MerkleWalkWitness
import R1RecordedRecoveryWitness
import R1MerkleLogExtension
import R1CanonicalRecoveryStability
import R1CanonicalTableRecovery
import R1InitialFrameNoMerkle
import R1C1BeforeFrameStability
import R1FirstReadCut
import R1C1TableStability
import R1FixedFrameNoMerkle
import R1LaterCommitmentStability

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1MerkleProgram, `R1CanonicalMerkleProgram, `R1CanonicalMerkleCollision, `R1CanonicalReadCollision, `R1ParsedTargetsFirstHit, `R1ParsedTargetsPrefixHit, `R1CanonicalMerkleRecovery, `R1CanonicalPredictedRecovery, `R1CanonicalFullTraceRecovery, `R1CommitmentRootFrames, `R1ThreeCommitmentFullTrace, `R1TraceTableMembership, `R1CanonicalLogMembership, `R1CanonicalLogSeparation, `R1MerkleNodeLookupExt, `R1MerkleNodeRecordUnique, `R1MerkleLeafLookupExt, `R1MerkleLeafRecordUnique, `R1MerkleLogExt, `R1MerkleWalkWitness, `R1RecordedRecoveryWitness, `R1MerkleLogExtension, `R1CanonicalRecoveryStability, `R1CanonicalTableRecovery, `R1InitialFrameNoMerkle, `R1C1BeforeFrameStability, `R1FirstReadCut, `R1C1TableStability, `R1FixedFrameNoMerkle, `R1LaterCommitmentStability]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
