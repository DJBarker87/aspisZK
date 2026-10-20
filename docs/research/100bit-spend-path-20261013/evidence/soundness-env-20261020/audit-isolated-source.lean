import Lean
open Lean
#eval show IO Unit from do
  let owners : List Name := [`ExtractedSourceFull25Frames, `ExtractedSourceDigestAddresses, `RawSourceDigestLog, `ExtractedSourceSemanticSampler, `ExtractedSourceDigestOracle, `RawSamplerSuffixSourceFrames, `Stage2ContinuationTypes, `WireTx2BinaryBodies, `WireTx2Records, `WireTx2SliceFacts, `WireTx2LeafBodies, `WireTx2LeafCalls, `BinWirePublicLengths, `ExtractedTerminalDecoderSuccess, `BinWireEnvelopeLengths, `R1PoseidonMap, `R1NoteHashMap, `R1AppendBindingMap, `R1SpendRelationMap, `R1SpendBaseDescent, `R1TraceSpendWitness, `R1CandidateBaseProjection, `R1InputWitness, `R1AppendSemantics, `R1SpendRelationExtraction, `R1ConcreteSpendExtraction, `R1CanonicalAddressEmbedding, `CanonicalRawTrace, `UnifiedDecoderCanonical, `PartialAddressImage]
  for owner in owners do
    let env ← importModules #[{ module := owner }] {} (loadExts := true)
    let action : CoreM Unit := do
      let current ← getEnv
      for entry in current.constants.toList do
        let decl := entry.1
        if let some idx := current.getModuleIdxFor? decl then
          let moduleOwner := current.header.moduleNames[idx]!
          if moduleOwner == owner then
            let axs ← collectAxioms decl
            liftIO <| IO.println s!"S_AXIOMS {moduleOwner} | {decl} | {axs.toList}"
    CoreM.toIO' action { fileName := "isolated-axiom-audit", fileMap := FileMap.ofString "" } { env := env }
