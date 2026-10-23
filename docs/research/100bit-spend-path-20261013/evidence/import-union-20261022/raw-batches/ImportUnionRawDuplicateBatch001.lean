import Lean
open Lean
private def readComplete (p : System.FilePath) : IO ModuleData := do
  let mut files := #[p]
  for suffix in [".server", ".private"] do
    let q : System.FilePath := p.toString ++ suffix
    if ← q.pathExists then files := files.push q
  let parts ← readModuleDataParts files
  let some (data, _) := parts.toList.getLast? | throw (IO.userError "Empty module")
  pure data

#eval show IO Unit from do
  let requests : Array (String × Array (String × String)) := #[("AspisR1.OraclePortRuntimeBindingC7.originalWith.eq_1", #[("OraclePortFrozen2Join", "theorem"), ("OraclePortRefineJoinConsumer", "theorem")]),
("AspisR1.OracleProgramReplay.oracleOf.congr_simp", #[("RawCutWordsFromRunExecutable", "theorem"), ("RawCutWordsFromRunExecutableBin", "theorem"), ("BinFrameReplayReads", "theorem")]),
("AspisR1.PoseidonM31DotReads.remaining.eq_1", #[("PoseidonM31DotChunkModel", "theorem"), ("PoseidonM31DotRemainingAlgebra", "theorem")]),
("AspisR1.PoseidonM31DotReads.remaining.eq_2", #[("PoseidonM31DotChunkModel", "theorem"), ("PoseidonM31DotRemainingAlgebra", "theorem")]),
("AspisR1.PoseidonM31DotReads.remaining.eq_def", #[("PoseidonM31DotChunkModel", "theorem"), ("PoseidonM31DotRemainingAlgebra", "theorem")]),
("AspisR1.PublicByteCodec.PrefixCodec.fixed.eq_1", #[("R1PublicByteCodecLaws", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.PrefixCodec.option.eq_1", #[("R1PublicByteCodecLaws", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.PrefixCodec.pair.eq_1", #[("R1PublicByteCodecLaws", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.PrefixCodec.transport.eq_1", #[("R1PublicByteCodecLaws", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.digestCodec.eq_1", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.encode.eq_1", #[("R1PublicByteCodecLaws", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.encodeDigest.eq_1", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.encodeFrontier.eq_1", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.fieldsCodec.eq_1", #[("R1PublicByteCodecLaws", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.frontierCodec.eq_1", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.m31Codec.eq_1", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.publicCodec.eq_1", #[("R1PublicByteCodecLaws", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.publicFieldsEquiv.eq_1", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.toFields.eq_1", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicByteCodec.variantCodec.eq_1", #[("R1PublicByteCodecLaws", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicCodecAgreement.encode_toPublic_eq_wire_encode", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicCodecAgreement.u64_emit_eq_index_encode", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicCodecAgreement.u64_emit_eq_index_encode._proof_1", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicCodecAgreement.u64_emit_eq_index_encode._proof_2", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicFieldBlockCodec.encodeFrontier.eq_1", #[("PublicCodecAgreement", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.PublicInitFrame.addr.congr_simp", #[("R1InitialFrameNoMerkle", "theorem"), ("R1UnifiedSampler", "theorem"), ("R1InitialDecoder", "theorem"), ("R1InitialWalkCells", "theorem")]),
("AspisR1.PublicInitFrame.domain.eq_1", #[("R1InitialFrameNoMerkle", "theorem"), ("R1PublicInitAbsorbSeparation", "theorem"), ("RawTranscriptFrameBytes", "theorem")]),
("AspisR1.PublicInitFrame.row0.congr_simp", #[("R1UnifiedSampler", "theorem"), ("R1InitialTrace", "theorem")]),
("AspisR1.PublicOptionShape.check.congr_simp", #[("R1SemanticPublicWire", "theorem"), ("SpendRelation", "theorem"), ("R1PublicByteCodecLaws", "theorem")]),
("AspisR1.PublicRawCore.afterBytes.eq_1", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.PublicRawCore.afterWords.eq_1", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.PublicRawCore.encode.eq_1", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.PublicRawCore.encode.eq_2", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.PublicRawCore.encodeWords.eq_1", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.PublicRawCore.frontierWords.eq_1", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.PublicRawCore.headerWords.eq_1", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.PublicRawCore.serialize.eq_1", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.PublicRawCore.words.eq_1", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.PublicRawCore.words.eq_2", #[("PublicExtractedRawBridge431", "theorem"), ("PublicRawCoreAgreement", "theorem")]),
("AspisR1.RRConcreteState.model.eq_1", #[("RRConcreteStatePolynomialView", "theorem"), ("RRConcreteNormalizeChildTotal", "theorem")]),
("AspisR1.RRProgramTraversal.collectProgram.eq_1", #[("RRProgramQueryBound", "theorem"), ("RRProgramRecoveryContracts", "theorem"), ("RRTraversalWriterM10", "theorem")]),
("AspisR1.RRProgramTraversal.collectProgram.eq_2", #[("RRProgramQueryBound", "theorem"), ("RRProgramRecoveryContracts", "theorem"), ("RRTraversalWriterM10", "theorem")]),
("AspisR1.RRProgramTraversal.collectProgram.eq_def", #[("RRProgramQueryBound", "theorem"), ("RRProgramRecoveryContracts", "theorem"), ("RRTraversalWriterM10", "theorem")]),
("AspisR1.RRProgramTraversal.mapOption.eq_1", #[("RRProgramMeanTools", "theorem"), ("RRTraversalWriterM10", "theorem")]),
("AspisR1.RRProgramTraversal.optionBind.eq_1", #[("RRProgramMeanTools", "theorem"), ("RRProgramWalkRelation", "theorem"), ("RRTraversalWriterM10", "theorem")]),
("AspisR1.RRProgramTraversal.walkChildren.eq_1", #[("RRProgramWalkRelation", "theorem"), ("RRTraversalWriterM10", "theorem")]),
("AspisR1.RRProgramTraversal.walkChildren.eq_2", #[("RRProgramWalkRelation", "theorem"), ("RRTraversalWriterM10", "theorem")]),
("AspisR1.RRProgramTraversal.walkChildren.eq_def", #[("RRProgramWalkRelation", "theorem"), ("RRTraversalWriterM10", "theorem")]),
("AspisR1.RawCommitmentFrameReplay.stateBefore.eq_1", #[("RawCommitmentFrameReplayCorrect", "theorem"), ("BinFrameReplayReads", "theorem")]),
("AspisR1.RawCommitmentFrameReplay.stateBefore.eq_2", #[("RawCommitmentFrameReplayCorrect", "theorem"), ("BinFrameReplayReads", "theorem")]),
("AspisR1.RawCommitmentFrameReplay.stateBefore.eq_def", #[("RawCommitmentFrameReplayCorrect", "theorem"), ("BinFrameReplayReads", "theorem")]),
("AspisR1.RawCutProverCompiler.verifier.eq_1", #[("RawCutLiteralInitialAdvanceRead", "theorem"), ("RawCutLiteralSamplerOrder", "theorem"), ("RWireRawCutLiteralSamplerOrder", "theorem")]),
("AspisR1.RawCutTranscriptRun.proof.eq_1", #[("RawCompiledChecksOriginalSchedule", "theorem"), ("RawCompiledChecksOriginalScheduleBin", "theorem")]),
("AspisR1.RawCutWordsFromView.frameFromView.eq_1", #[("RawCutWordsFromRunExecutable", "theorem"), ("RawCutWordsFromRunExecutableBin", "theorem")]),
("AspisR1.RawTranscriptFrameBytes.advance.eq_1", #[("BinFrameConstructionWork", "theorem"), ("BinFrameLookupWork", "theorem")]),
("AspisR1.RawTranscriptFrameBytes.openingDomain.eq_1", #[("BinFrameConstructionWork", "theorem"), ("BinFrameLookupWork", "theorem")]),
("AspisR1.RawTranscriptFrameBytes.reseed.eq_1", #[("BinFrameConstructionWork", "theorem"), ("BinFrameLookupWork", "theorem")]),
("AspisR1.RawTranscriptFrameBytes.rowZero.eq_1", #[("BinFrameConstructionWork", "theorem"), ("BinFrameLookupWork", "theorem")]),
("AspisR1.ReseedPrefix.raw.eq_1", #[("R1ReseedSeparation", "theorem"), ("R1ReseedPrefixCells", "theorem")]),
("AspisR1.RetainedFieldByteCodec.decodeM31LE.eq_1", #[("R1M31ParserRefinement", "theorem"), ("R1ListFieldCodec", "theorem")]),
("AspisR1.SelectedTranscriptParams.params.eq_1", #[("R1LiteralTranscript", "theorem"), ("R1SelectedIndexedRead", "theorem")]),
("AspisR1.SemanticPublicModel.exactPublic.eq_1", #[("ScalarSuffixPacking", "theorem"), ("DigestFixedPrefixR0P", "theorem")]),
("AspisR1.SemanticPublicWire.afterBytes.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("R1SemanticPublicWireSound", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.SemanticPublicWire.decode.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("R1SemanticPublicWireSound", "theorem"), ("PublicParserWork", "theorem")]),
("AspisR1.SemanticPublicWire.decode.eq_2", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("R1SemanticPublicWireSound", "theorem"), ("PublicParserWork", "theorem")]),
("AspisR1.SemanticPublicWire.decodeAfter.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("PublicParserWork", "theorem")]),
("AspisR1.SemanticPublicWire.decodeTransfer.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("PublicParserWork", "theorem")]),
("AspisR1.SemanticPublicWire.decodeWithdrawal.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("PublicParserWork", "theorem")]),
("AspisR1.SemanticPublicWire.encode.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("R1SemanticPublicWireSound", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.SemanticPublicWire.encode.eq_2", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("R1SemanticPublicWireSound", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.SemanticPublicWire.expect.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("R1SemanticPublicWireSound", "theorem")]),
("AspisR1.SemanticPublicWire.expect.eq_2", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("R1SemanticPublicWireSound", "theorem")]),
("AspisR1.SemanticPublicWire.header.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("R1SemanticPublicWireSound", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.SemanticPublicWire.readDigest.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("PublicParserWork", "theorem")]),
("AspisR1.SemanticPublicWire.readField.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("PublicParserWork", "theorem")]),
("AspisR1.SemanticPublicWire.readFrontier.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("PublicParserWork", "theorem")]),
("AspisR1.SemanticPublicWire.readIndex.eq_1", #[("R1SemanticPublicWireRoundTrip", "theorem"), ("PublicParserWork", "theorem")]),
("AspisR1.SemanticPublicWire.toPublic.eq_1", #[("R1SemanticPublicWireInjective", "theorem"), ("R1SemanticPublicWireSurjective", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.SemanticPublicWire.toPublic.eq_2", #[("R1SemanticPublicWireInjective", "theorem"), ("R1SemanticPublicWireSurjective", "theorem"), ("R1PublicCodecAgreement", "theorem")]),
("AspisR1.SharedBinaryRecordGrammar.leafInput.eq_1", #[("BinSharedGrammarBridge", "theorem"), ("R1Z.SharedGrammarBridgeBin", "theorem")]),
("AspisR1.SpendDataMap.digest.eq_1", #[("R1SpendRelationMap", "theorem"), ("DigestFamilyFieldTransport", "theorem")]),
("AspisR1.SpendDataMap.mapPublic.eq_1", #[("R1AppendBindingMap", "theorem"), ("DigestFamilyFieldTransport", "theorem")]),
("AspisR1.SpendRelation.changeCommitment.eq_1", #[("R1SpendRelationMap", "theorem"), ("R1SpendRelationExtraction", "theorem")]),
("AspisR1.SpendRelation.outputPair.eq_1", #[("R1AppendBindingMap", "theorem"), ("R1SpendRelationExtraction", "theorem")]),
("AspisR1.SpendRelation.recipientCommitment.eq_1", #[("R1SpendRelationMap", "theorem"), ("R1SpendRelationExtraction", "theorem")]),
("AspisR1.TraceAppend.firstReads_le_append", #[("TraceAppend", "theorem"), ("R1TraceAppend", "theorem")]),
("AspisR1.TraceAppend.firstReads_le_append._proof_1", #[("TraceAppend", "theorem"), ("R1TraceAppend", "theorem")]),
("AspisR1.TraceAppend.hitsBad_of_prefix", #[("TraceAppend", "theorem"), ("R1TraceAppend", "theorem")]),
("AspisR1.TraceAppend.tableBefore_append", #[("TraceAppend", "theorem"), ("R1TraceAppend", "theorem")]),
("AspisR1.TraceAppend.tableBefore_append._simp_1", #[("TraceAppend", "theorem"), ("R1TraceAppend", "theorem")]),
("AspisR1.TraceAppend.traceFrom_append", #[("TraceAppend", "theorem"), ("R1TraceAppend", "theorem")]),
("AspisR1.TranscriptView.liftChallenge.eq_1", #[("R1LiteralSemanticDensity", "theorem"), ("R1LiteralOrdinaryDensity", "theorem"), ("R1UnifiedRecords", "theorem"), ("R1LiteralGammaSample", "theorem")]),
("AspisR1.TypedRecoveredWords.laneSubfield.eq_1", #[("R1LiteralTypedContext", "theorem"), ("R1CandidateBaseProjection", "theorem")]),
("AspisR1.UnifiedPrefixedReads.trace.congr_simp", #[("R1UnifiedSemanticRecovery", "theorem"), ("R1UnifiedSemanticFacts", "theorem"), ("R1UnifiedRhoInjection", "theorem")]),
("AspisR1.UnifiedProtocol.protocol.congr_simp", #[("R1UnifiedSemanticCase", "theorem"), ("R1UnifiedReseedCase", "theorem"), ("R1UnifiedOpeningCase", "theorem"), ("R1UnifiedQueryCase", "theorem"), ("R1UnifiedRhoCase", "theorem")]),
("AspisR1.UnifiedQueryRun.rhoAddress.congr_simp", #[("RawPublicRhoRecovery", "theorem"), ("R1UnifiedRhoInjection", "theorem")]),
("AspisR1.UnifiedRecords.absorbed.congr_simp", #[("R1UnifiedSteps", "theorem"), ("R1UnifiedRecordCompletion", "theorem")]),
("AspisR1.UnifiedSampler.absorb.eq_1", #[("R1UnifiedRecords", "theorem"), ("R1UnifiedContinuation", "theorem")]),
("AspisR1.UnifiedSampler.liftQuery.eq_1", #[("R1UnifiedQueryRun", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.UnifiedSampler.messageValid._sparseCasesOn_1.else_eq", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1UnifiedSamplerLaw", "theorem")])]
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let out ← IO.FS.Handle.mk "evidence/raw-batch-001.jsonl" .write
  let mut types : Std.HashMap String Expr := {}
  let mut equal : Std.HashMap String Bool := {}
  let mut found : Std.HashMap String (Array String) := {}
  let owners := requests.foldl (fun acc (_, os) => os.foldl (fun a (o, _) => if a.contains o then a else a.push o) acc) (#[] : Array String)
  for owner in owners do
    let wanted := requests.filter (fun (_, os) => os.any (fun (o, _) => o == owner))
    let mut file : Option System.FilePath := none
    for root in roots do
      let p : System.FilePath := root ++ "/" ++ owner.replace "." "/" ++ ".olean"
      if ← p.pathExists then
        file := some p
        break
    let some p := file | throw (IO.userError s!"Missing {owner}")
    let data ← readComplete p
    for ci in data.constants do
      let name := ci.name.toString
      if wanted.any (fun (n, _) => n == name) then
        found := found.insert name ((found[name]?.getD #[]).push owner)
        if let some old := types[name]? then
          equal := equal.insert name ((equal[name]?.getD true) && old == ci.type)
        else
          types := types.insert name ci.type
        out.putStrLn ("RAW_DUP_TYPE " ++ (Json.arr #[toJson name, toJson owner, toJson ((hash ci.type).toNat)]).compress)
  for (name, os) in requests do
    let actual := found[name]?.getD #[]
    unless actual.size == os.size && os.all (fun (o, _) => actual.contains o) do
      throw (IO.userError s!"Missing duplicate owner for {name}")
    let sameType := equal[name]?.getD true
    let allowed := os.all (fun (_, k) => k == "theorem") && sameType
    out.putStrLn ("RAW_DUP " ++ (Json.arr #[toJson name, toJson os, toJson sameType, toJson allowed]).compress)
  out.flush
  IO.println ("RAW_BATCH_COMPLETE " ++ toString requests.size)
