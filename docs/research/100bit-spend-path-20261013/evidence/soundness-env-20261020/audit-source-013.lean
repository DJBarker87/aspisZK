import Lean
import R1QueryBackgroundChain
import R1UnifiedQueryDecoder
import R1JointUnifiedDecoder
import R1UnifiedLabels
import R1PublicInitAbsorbSeparation
import R1UnifiedDecoder
import R1CanonicalByteAddress
import BackgroundCanonicalLabels
import OccupancyRangeTraversal
import BinMerkle32Path
import BinMerkle32Leaf
import BinMerkleProgram
import BinMultiproof
import BinMerkleTable
import BinBatchDedup
import BinMerkleNodeCodec
import R1Merkle32Path
import R1MerkleNodeCodec
import R1NaturalProjection
import R1FirstFold
import R1RoundPairing
import R1FoldCoefficientBridge
import R0C.SemStatement
import R0P.Core
import R0P.PoseidonConstants
import R0P.CoreExt
import R0P.Path
import R0P.Poseidon
import R0P.Positivity
import R0P.Value

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1QueryBackgroundChain, `R1UnifiedQueryDecoder, `R1JointUnifiedDecoder, `R1UnifiedLabels, `R1PublicInitAbsorbSeparation, `R1UnifiedDecoder, `R1CanonicalByteAddress, `BackgroundCanonicalLabels, `OccupancyRangeTraversal, `BinMerkle32Path, `BinMerkle32Leaf, `BinMerkleProgram, `BinMultiproof, `BinMerkleTable, `BinBatchDedup, `BinMerkleNodeCodec, `R1Merkle32Path, `R1MerkleNodeCodec, `R1NaturalProjection, `R1FirstFold, `R1RoundPairing, `R1FoldCoefficientBridge, `R0C.SemStatement, `R0P.Core, `R0P.PoseidonConstants, `R0P.CoreExt, `R0P.Path, `R0P.Poseidon, `R0P.Positivity, `R0P.Value]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
