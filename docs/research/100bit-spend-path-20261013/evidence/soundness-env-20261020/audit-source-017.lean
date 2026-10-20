import Lean
import R1ParsedTargetsCollision
import R1MerkleChildTargets
import R1FixedOffsetTarget
import R1CommitmentRootTargets
import R1CombinedMerkleTargets
import RawByteCollisionTargets
import BinRawByteCollisionTargets
import BinMerkleRecovery
import BinMerkleLeafRecovery
import BinMerkleLeafCodec
import BinMerkleRecordedLog
import BinMerkleTraceInputs
import BinMerkleLogRecovery
import BinRawByteCutRecovery
import BinMerkleWalkWitness
import BinRecordedRecoveryWitness
import BinMerkleLogExtension
import BinRawByteCutStability
import R1CanonicalByteHash
import R1MerkleTable
import R1MerkleRecovery
import R1Merkle32Leaf
import R1MerkleLeafRecovery
import R1MerkleLeafCodec
import R1MerkleRecordedLog
import R1MerkleRecordedTargets
import R1MerkleTraceInputs
import R1MerkleLogRecovery
import R1CanonicalOracleLog
import R1CanonicalLogInputs

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1ParsedTargetsCollision, `R1MerkleChildTargets, `R1FixedOffsetTarget, `R1CommitmentRootTargets, `R1CombinedMerkleTargets, `RawByteCollisionTargets, `BinRawByteCollisionTargets, `BinMerkleRecovery, `BinMerkleLeafRecovery, `BinMerkleLeafCodec, `BinMerkleRecordedLog, `BinMerkleTraceInputs, `BinMerkleLogRecovery, `BinRawByteCutRecovery, `BinMerkleWalkWitness, `BinRecordedRecoveryWitness, `BinMerkleLogExtension, `BinRawByteCutStability, `R1CanonicalByteHash, `R1MerkleTable, `R1MerkleRecovery, `R1Merkle32Leaf, `R1MerkleLeafRecovery, `R1MerkleLeafCodec, `R1MerkleRecordedLog, `R1MerkleRecordedTargets, `R1MerkleTraceInputs, `R1MerkleLogRecovery, `R1CanonicalOracleLog, `R1CanonicalLogInputs]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
