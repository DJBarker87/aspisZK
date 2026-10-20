import Lean
import R1TypedRecoveryStability
import R1FixedWidthReconstruction
import R1FixedWidthDecodedSlices
import R1StrictWideByteCodec
import R1WideExactLimbCodec
import R1FoldedLeafCodec
import R1MerkleIndexGeometry
import R1FoldedRecoveredWord
import R1CanonicalTypedOpening
import R1CanonicalCutOpening
import R1LiteralTypedWords
import R1CanonicalCutTypedProjection
import R1CanonicalCutWordProjection
import R1SelectedChallengeMapCore
import R1PublicFieldBlockCodec
import R1PublicIndexCodec
import R1PublicIndexListCodec
import R1PublicByteCursor
import PublicOptionShape
import R1SemanticPublicWire
import R1SemanticPublicWireRoundTrip
import R1SemanticPublicWireSound
import R1SemanticPublicWireInjective
import R1SemanticPublicByteBinding
import R1SemanticPublicWireSurjective
import R1SemanticPublicCodecComplete
import R1SelectedTranscriptParams
import RawByteCutRecovery
import RawByteCutStability
import BinCombinedMerkleCollision

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1TypedRecoveryStability, `R1FixedWidthReconstruction, `R1FixedWidthDecodedSlices, `R1StrictWideByteCodec, `R1WideExactLimbCodec, `R1FoldedLeafCodec, `R1MerkleIndexGeometry, `R1FoldedRecoveredWord, `R1CanonicalTypedOpening, `R1CanonicalCutOpening, `R1LiteralTypedWords, `R1CanonicalCutTypedProjection, `R1CanonicalCutWordProjection, `R1SelectedChallengeMapCore, `R1PublicFieldBlockCodec, `R1PublicIndexCodec, `R1PublicIndexListCodec, `R1PublicByteCursor, `PublicOptionShape, `R1SemanticPublicWire, `R1SemanticPublicWireRoundTrip, `R1SemanticPublicWireSound, `R1SemanticPublicWireInjective, `R1SemanticPublicByteBinding, `R1SemanticPublicWireSurjective, `R1SemanticPublicCodecComplete, `R1SelectedTranscriptParams, `RawByteCutRecovery, `RawByteCutStability, `BinCombinedMerkleCollision]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
