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
  let requests : Array (String × Array (String × String)) := #[("AddEquiv.mk.congr_simp", #[("Mathlib.Algebra.Module.Equiv.Basic", "theorem"), ("Mathlib.Algebra.Group.Finsupp", "theorem"), ("Mathlib.Algebra.DirectSum.Basic", "theorem")]),
("AddEquivClass.toAddEquiv.congr_simp", #[("Mathlib.LinearAlgebra.FreeModule.Basic", "theorem"), ("Mathlib.LinearAlgebra.Dimension.Basic", "theorem"), ("Mathlib.RingTheory.IsTensorProduct", "theorem"), ("Mathlib.Algebra.Order.Hom.TypeTags", "theorem")]),
("AddHom.mk.congr_simp", #[("Mathlib.Algebra.Module.Equiv.Basic", "theorem"), ("Mathlib.Algebra.Module.Submodule.Equiv", "theorem"), ("Mathlib.LinearAlgebra.Finsupp.Defs", "theorem")]),
("AddMonoidHom.mk'.congr_simp", #[("Mathlib.Analysis.Normed.Group.Hom", "theorem"), ("Mathlib.Topology.Instances.AddCircle.Real", "theorem")]),
("AddMonoidHom.mk.congr_simp", #[("Mathlib.Algebra.Group.Equiv.TypeTags", "theorem"), ("Mathlib.Algebra.BigOperators.Finsupp.Basic", "theorem"), ("Mathlib.Data.DFinsupp.BigOperators", "theorem"), ("Mathlib.Algebra.Group.AddChar", "theorem")]),
("AddMonoidHomClass.toAddMonoidHom.congr_simp", #[("Mathlib.Algebra.Group.Equiv.Basic", "theorem"), ("Mathlib.Algebra.Order.Hom.TypeTags", "theorem")]),
("AddSubgroup.mk.congr_simp", #[("Mathlib.Analysis.Normed.Group.AddCircle", "theorem"), ("Mathlib.Topology.Algebra.Valued.ValuationTopology", "theorem")]),
("AddSubmonoid.comap.congr_simp", #[("Mathlib.Algebra.Order.Star.Basic", "theorem"), ("Mathlib.LinearAlgebra.DFinsupp", "theorem")]),
("AddSubmonoid.map.congr_simp", #[("Mathlib.GroupTheory.Finiteness", "theorem"), ("Mathlib.Algebra.Order.Star.Basic", "theorem")]),
("Aeneas.Std.Array.make.congr_simp", #[("ExtractedQM31SamplerBytes", "theorem"), ("AspisR1EbyKPushWideToQ", "theorem"), ("R1Z.ProverCommitSimulatorCoin18", "theorem"), ("R1Z.ProverCommitSaltSource", "theorem"), ("R0Z.PoseidonExtracted", "theorem"), ("R1Z.BuilderBankExtracted", "theorem"), ("R1Z.BuilderStdArray", "theorem"), ("R1Z.ProverCommitReferenceSource", "theorem"), ("R1Z.ProverCommitStreamSource", "theorem"), ("ExtractedMaskPreparedState", "theorem"), ("ExtractedPreparationSerializerWhole", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof", "theorem"), ("AspisR1.CopyPatternRegistrySource", "theorem")]),
("Aeneas.Std.Array.make.eq_1", #[("AspisV8R19.SqueezeSourceExecution", "theorem"), ("AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11", "theorem"), ("AspisR1EbyKPushWideToQ", "theorem"), ("S3VariantRowBodyProbe", "theorem"), ("S3InactiveModelBridge", "theorem"), ("PublicExtractedRawBridge431", "theorem"), ("WithdrawalValidationAmount431", "theorem"), ("R1Z.ProverCommitSaltBytes", "theorem"), ("R1Z.BuilderStdModels", "theorem"), ("ExtractedMaskCoefficientSchedule", "theorem"), ("SumHighSingleRange", "theorem"), ("SelectorValueLaneMap", "theorem"), ("CopyResidualExact", "theorem"), ("AspisR1.PoseidonPreparedIndexComponentsCanonical", "theorem"), ("AspisR1PoseidonPreparedStateCells", "theorem"), ("AspisR1.PoseidonPreparedInputCellValues", "theorem"), ("AspisR1.PoseidonPreparedStateUnique", "theorem")]),
("Aeneas.Std.I32.ofInt.congr_simp", #[("Aeneas.Tactic.Step.Step", "theorem"), ("SelectorRowCall", "theorem"), ("SelectorValueLaneTailConstants", "theorem")]),
("Aeneas.Std.Isize.ofInt.congr_simp", #[("ActualDecodeKFieldParserTransport", "theorem"), ("R1CandidateParserSupport", "theorem"), ("ExtractedAdapterReconstructSuccess", "theorem"), ("CopyLinkWeightExact", "theorem")]),
("Aeneas.Std.Option.ofResult.eq_1", #[("Aeneas.Std.Scalar.CheckedOps.Add", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Div", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Mul", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Rem", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Sub", "theorem")]),
("Aeneas.Std.Option.ofResult.eq_2", #[("Aeneas.Std.Scalar.CheckedOps.Add", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Div", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Mul", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Rem", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Sub", "theorem")]),
("Aeneas.Std.U32.ofNat.congr_simp", #[("Aeneas.Command.Decompose.Tests", "theorem"), ("Aeneas.Command.Decompose.TestsBig", "theorem"), ("Aeneas.Do.Tests", "theorem"), ("Aeneas.Tactic.Solver.BvTac.Lemmas", "theorem"), ("R0Z.BlockRefine", "theorem"), ("R0Z.PoseidonExtracted", "theorem"), ("R0Z.WriterRefineMerge", "theorem"), ("R0Z.WriterRefinePathModel", "theorem"), ("R1Z.BuilderBankExtracted", "theorem"), ("ExtractedMaskReducer", "theorem"), ("ExtractedMaskNeg", "theorem"), ("AspisR1.CopyPatternRegistrySource", "theorem"), ("CopyLinkBitArithmetic", "theorem")]),
("Aeneas.Std.U64.ofNat.congr_simp", #[("Aeneas.Tactic.Solver.BvTac.Lemmas", "theorem"), ("R0Z.PoseidonRefine", "theorem"), ("ExtractedMaskQmPackBase4SourceArithmetic", "theorem"), ("TerminalDigestBranchBits", "theorem"), ("CopyLinkBitArithmetic", "theorem"), ("RawPoseidonExternalRowClosure", "theorem"), ("AspisR1.PoseidonPreparedSum3DecodedWithBuild", "theorem")]),
("Aeneas.Std.U8.ofNat.congr_simp", #[("Aeneas.Command.Decompose.Tests", "theorem"), ("Aeneas.Tactic.Solver.BvTac.Lemmas", "theorem"), ("AspisR1SimulatorCoin18.Funs", "theorem"), ("AspisR1SelectedMaskProbe.Funs", "theorem")]),
("Aeneas.Std.Usize.ofNat.congr_simp", #[("Aeneas.Std.Array.Array", "theorem"), ("Aeneas.Std.Core.Iter", "theorem")]),
("Aeneas.Std.core.convert.num.FromU32Bool.from.eq_1", #[("R1Z.BuilderRecordsAdmission", "theorem"), ("CopyLinkWeightExact", "theorem")]),
("Aeneas.Std.core.slice.Slice.iter.eq_1", #[("R1Z.BuilderAdmissionCanonical", "theorem"), ("R1Z.BuilderColumns", "theorem")]),
("Aeneas.Std.core.slice.iter.IteratorSliceIter.next.eq_1", #[("PublicSerializerFieldsRefinement431", "theorem"), ("SumHighSingleRange", "theorem"), ("SelectorExpansionOuter", "theorem")]),
("Aeneas.Std.instBEqResult.beq._sparseCasesOn_1.else_eq", #[("Aeneas.Std.Scalar.CheckedOps.Add", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Div", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Mul", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Rem", "theorem"), ("Aeneas.Std.Scalar.CheckedOps.Sub", "theorem")]),
("AlgEquiv.ofAlgHom.congr_simp", #[("Mathlib.Algebra.MvPolynomial.Equiv", "theorem"), ("Mathlib.RingTheory.TensorProduct.MonoidAlgebra", "theorem"), ("Mathlib.RingTheory.Localization.AtPrime.Basic", "theorem"), ("Mathlib.RingTheory.TensorProduct.Quotient", "theorem")]),
("AlgEquiv.ofLinearEquiv.congr_simp", #[("Mathlib.LinearAlgebra.Matrix.ToLin", "theorem"), ("Mathlib.RingTheory.IsTensorProduct", "theorem")]),
("AlgEquivClass.toAlgEquiv.congr_simp", #[("Mathlib.Algebra.Algebra.Spectrum.Basic", "theorem"), ("Mathlib.LinearAlgebra.Determinant", "theorem"), ("Mathlib.LinearAlgebra.Trace", "theorem")]),
("AlgHom.ofLinearMap.congr_simp", #[("Mathlib.RingTheory.TensorProduct.Basic", "theorem"), ("Mathlib.RingTheory.AdicCompletion.Algebra", "theorem")]),
("AlgHom.restrictDomain.eq_1", #[("Mathlib.RingTheory.Trace.Basic", "theorem"), ("Mathlib.RingTheory.Norm.Basic", "theorem")]),
("Algebra.TensorProduct.cancelBaseChange.congr_simp", #[("Mathlib.RingTheory.SurjectiveOnStalks", "theorem"), ("Mathlib.RingTheory.TensorProduct.Finite", "theorem")]),
("Algebra.lsmul.congr_simp", #[("Mathlib.LinearAlgebra.TensorProduct.Tower", "theorem"), ("Mathlib.Algebra.Polynomial.Module.AEval", "theorem"), ("Mathlib.Analysis.Normed.Operator.Mul", "theorem")]),
("Array.anyM.loop.congr_simp", #[("Init.Data.Array.Lemmas", "theorem"), ("Init.Internal.Order.Lemmas", "theorem")]),
("Array.foldlM.loop.eq_1", #[("Init.Data.Array.Lemmas", "theorem"), ("Init.Internal.Order.Lemmas", "theorem")]),
("Array.insertIdx.congr_simp", #[("Init.Data.List.ToArray", "theorem"), ("Init.Data.Array.BinSearch", "theorem")]),
("Array.isEmpty.eq_1", #[("Init.Data.Array.DecidableEq", "theorem"), ("Init.Data.List.ToArray", "theorem")]),
("Array.set!.eq_1", #[("Std.Tactic.BVDecide.LRAT.Internal.Formula.Lemmas", "theorem"), ("CompPoly.Univariate.NTTFast.Correctness.Basic", "theorem")]),
("AspisCircleGroupOrder.X.eq_1", #[("AspisFormal.V5FriExactLineDomains", "theorem"), ("AspisFormal.V5FriCircleEncoderDistance", "theorem")]),
("AspisPool.AlgorithmicCircleDecoderV7.agreementCount.eq_1", #[("Wide.EncoderLinearity", "theorem"), ("Wide.MultiplicityThreeGS", "theorem"), ("GSWideExactAgreementInputs", "theorem")]),
("AspisPool.AlgorithmicCircleDecoderV7.closeAtLeast.eq_1", #[("Wide.MultiplicityThreeGS", "theorem"), ("GSRuntimeInitialDistanceEncoderBridge", "theorem"), ("GSRuntimeFinalDistanceEncoderBridge", "theorem")]),
("AspisR0.Opening.eqWeight.eq_1", #[("R0P.SemHonest", "theorem"), ("R0P.SemDeg", "theorem")]),
("AspisR0.Opening.extraDefect.eq_1", #[("R0.BadSetBounds", "theorem"), ("R0.OpeningAlgebra", "theorem")]),
("AspisR0.Opening.imagePolynomial.eq_1", #[("R0.BadSetBounds", "theorem"), ("R0.OpeningAlgebra", "theorem")]),
("AspisR0.Opening.pointDefect.eq_1", #[("R0.BadSetBounds", "theorem"), ("R0.OpeningAlgebra", "theorem")]),
("AspisR0.Opening.pointPolynomial.eq_1", #[("R0.BadSetBounds", "theorem"), ("R0.OpeningAlgebra", "theorem")]),
("AspisR0.RoundNormalization.dot.eq_1", #[("R0.RoundNormalization", "theorem"), ("R0.OpeningWeights", "theorem")]),
("AspisR1.AbsorptionCallback.sourceCell.eq_1", #[("InitialArrayCallback", "theorem"), ("AbsorptionLiteralExecution", "theorem")]),
("AspisR1.AppendPath.step.eq_1", #[("CachedWitnessHashM10", "theorem"), ("R1Z.BuilderSpendRelation", "theorem")]),
("AspisR1.BinCanonicalCutWords.rawC1Map.eq_1", #[("RawCutRecordedWordsExecutableBin", "theorem"), ("RawCutRecordedWordsBoundedBin", "theorem")]),
("AspisR1.BinCanonicalCutWords.rawC2Map.eq_1", #[("RawCutRecordedWordsExecutableBin", "theorem"), ("RawCutRecordedWordsBoundedBin", "theorem")]),
("AspisR1.BinCanonicalCutWords.rawFoldedMap.eq_1", #[("RawCutRecordedWordsExecutableBin", "theorem"), ("RawCutRecordedWordsBoundedBin", "theorem")]),
("AspisR1.BinCombinedMerkleCollision.kappa.eq_1", #[("BinPerQueryNumeric", "theorem"), ("RWireCounterexamples", "theorem")]),
("AspisR1.BinMerkleLeafRecovery.recover.eq_1", #[("BinMerkleLogExtension", "theorem"), ("BinMerkleRecoveryReads", "theorem")]),
("AspisR1.BinRawByteCutStability.recoverAt.eq_1", #[("RawCutRecordedWordsExecutableBin", "theorem"), ("RawCutRecordedWordsBoundedBin", "theorem")]),
("AspisR1.CanonicalCutEnrichedTranscript.enrichMessage.eq_1", #[("LiteralDecoderEnrichment", "theorem"), ("RawCompiledTranscriptRoundAlignmentV7", "theorem"), ("CanonicalCutSemanticRead", "theorem")]),
("AspisR1.CanonicalCutEnrichedTranscript.enrichMessage.eq_2", #[("LiteralDecoderEnrichment", "theorem"), ("RawCompiledTranscriptRoundAlignmentV7", "theorem"), ("CanonicalCutSemanticRead", "theorem")]),
("AspisR1.CanonicalCutEnrichedTranscript.enrichMessage.eq_3", #[("LiteralDecoderEnrichment", "theorem"), ("RawCompiledTranscriptRoundAlignmentV7", "theorem"), ("CanonicalCutSemanticRead", "theorem")]),
("AspisR1.CanonicalCutEnrichedTranscript.enrichMessage.eq_4", #[("LiteralDecoderEnrichment", "theorem"), ("RawCompiledTranscriptRoundAlignmentV7", "theorem"), ("CanonicalCutSemanticRead", "theorem")]),
("AspisR1.CompPolyGeneralRootsProgram.generalRootsProgram.congr_simp", #[("RRFiniteRootSamplerNormalizedStateBridge", "theorem"), ("CompPolyGeneralFiniteRootSampler", "theorem")]),
("AspisR1.CompPolySequentialAbortBound.rootsProgram.eq_1", #[("CompPolyGeneralFiniteRootSampler", "theorem"), ("GSScalarSequentialScheduleM10", "theorem")]),
("AspisR1.EqualityValueAdapter.decode.eq_1", #[("OccupancyLiteralPrefixReadsV2", "theorem"), ("OccupancyLiteralTail", "theorem"), ("AspisR1TerminalDigestBindingCandidate.Exact", "theorem"), ("EqualityValueLoop", "theorem")]),
("AspisR1.ExtractedMaskQM31Exact.decode.eq_1", #[("ExtractedMaskConstants", "theorem"), ("ExtractedMaskQmPackBase4Arithmetic", "theorem"), ("ExtractedMaskScalarExact", "theorem"), ("ExtractedMaskPower26", "theorem"), ("AspisR1.PoseidonM31ConstantPow5", "theorem"), ("PoseidonRawLimbReassembly", "theorem"), ("AspisR1.PoseidonActualLowWeights", "theorem")]),
("AspisR1.ExtractedMaskTowerAdd.CanonicalCM.eq_1", #[("ExtractedMaskConstants", "theorem"), ("ExtractedMaskLinears", "theorem"), ("AspisR1.PoseidonActualLowWeights", "theorem")]),
("AspisR1.ExtractedMaskTowerAdd.CanonicalQM.eq_1", #[("ExtractedMaskConstants", "theorem"), ("ExtractedMaskLinears", "theorem"), ("AspisR1.PoseidonActualLowWeights", "theorem")]),
("AspisR1.FirstFold.channels.eq_1", #[("R1FirstFoldRestoration", "theorem"), ("R1Z.BatchedAlgebra", "theorem")]),
("AspisR1.LiteralOpeningEvents.withMessage.eq_1", #[("R1LiteralOpeningCoherence", "theorem"), ("R1LiteralQueryRhoTranscriptSupport", "theorem")]),
("AspisR1.LiteralOpeningView.View.mk.congr_simp", #[("R1LiteralOpeningFunctionalFacts", "theorem"), ("R1LiteralReadStability", "theorem"), ("CanonicalCutSemanticRead", "theorem")]),
("AspisR1.LiteralSemanticPrefix.parseMessage.eq_1", #[("R1LiteralSemanticMessageFacts", "theorem"), ("CanonicalCutSemanticRead", "theorem")]),
("AspisR1.LiteralSemanticPrefix.parseMessage.eq_2", #[("R1LiteralSemanticMessageFacts", "theorem"), ("CanonicalCutSemanticRead", "theorem")]),
("AspisR1.LiteralSemanticPrefix.parseMessage.eq_3", #[("R1LiteralSemanticMessageFacts", "theorem"), ("CanonicalCutSemanticRead", "theorem")]),
("AspisR1.LiteralSemanticPrefix.parseMessage.eq_4", #[("R1LiteralSemanticMessageFacts", "theorem"), ("CanonicalCutSemanticRead", "theorem")]),
("AspisR1.LiteralTranscript.erase.eq_1", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem")]),
("AspisR1.LiteralTranscript.erase.eq_2", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem")]),
("AspisR1.LiteralTranscript.erase.eq_3", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem")]),
("AspisR1.LiteralTranscript.erase.eq_4", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem")]),
("AspisR1.LiteralTranscript.samp.eq_1", #[("CanonicalCutEnrichedTranscript", "theorem"), ("R1LiteralRun", "theorem")]),
("AspisR1.LiteralTranscript.valid._sparseCasesOn_1.else_eq", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem"), ("CanonicalCutSemanticRead", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.LiteralTranscript.valid._sparseCasesOn_2.else_eq", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem"), ("CanonicalCutSemanticRead", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.LiteralTranscript.valid._sparseCasesOn_3.else_eq", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem"), ("CanonicalCutSemanticRead", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.LiteralTranscript.valid._sparseCasesOn_4.else_eq", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem"), ("CanonicalCutSemanticRead", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.LiteralTranscript.valid.eq_1", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem"), ("CanonicalCutSemanticRead", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.LiteralTranscript.valid.eq_2", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem"), ("CanonicalCutSemanticRead", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.LiteralTranscript.valid.eq_3", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem"), ("CanonicalCutSemanticRead", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.LiteralTranscript.valid.eq_4", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem"), ("CanonicalCutSemanticRead", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.LiteralTranscript.valid.eq_5", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1LiteralQueryBinding", "theorem"), ("CanonicalCutSemanticRead", "theorem"), ("R1LiteralQuerySample", "theorem")]),
("AspisR1.LiteralTypedWords.laneSubfield.eq_1", #[("R1LiteralTypedContext", "theorem"), ("R1LiteralSpendExtraction", "theorem")]),
("AspisR1.OraclePortCompactDraft.le32.eq_1", #[("OraclePortRootBytesC6", "theorem"), ("OraclePortCheckpointAbiC5", "theorem")]),
("AspisR1.OraclePortCompactDraft.slice.eq_1", #[("OraclePortStoredWidthsC4", "theorem"), ("OraclePortRootBytesC6", "theorem"), ("OraclePortCheckpointAbiC5", "theorem")]),
("AspisR1.OraclePortExperiment.original.eq_1", #[("OraclePortAdmission", "theorem"), ("OraclePortStoredProjectionC4", "theorem"), ("OraclePortSamplerPrefixDraft", "theorem")]),
("AspisR1.OraclePortFrozenOrder.hashLeaves.eq_1", #[("OraclePortFrozenOrderLeaves", "theorem"), ("OraclePortFrozenOrderBounds", "theorem")]),
("AspisR1.OraclePortFrozenOrder.hashLeaves.eq_2", #[("OraclePortFrozenOrderLeaves", "theorem"), ("OraclePortFrozenOrderBounds", "theorem")]),
("AspisR1.OraclePortFrozenOrder.hashLeaves.eq_def", #[("OraclePortFrozenOrderLeaves", "theorem"), ("OraclePortFrozenOrderBounds", "theorem")]),
("AspisR1.OraclePortFrozenOrder.runLevel.eq_1", #[("OraclePortFrozenOrderRecoveryStep", "theorem"), ("OraclePortFrozenOrderAccounting", "theorem")]),
("AspisR1.OraclePortFrozenOrder.runLevel.eq_2", #[("OraclePortFrozenOrderRecoveryStep", "theorem"), ("OraclePortFrozenOrderAccounting", "theorem")]),
("AspisR1.OraclePortFrozenOrder.runLevel.eq_3", #[("OraclePortFrozenOrderRecoveryStep", "theorem"), ("OraclePortFrozenOrderAccounting", "theorem")]),
("AspisR1.OraclePortFrozenOrder.runLevel.eq_4", #[("OraclePortFrozenOrderRecoveryStep", "theorem"), ("OraclePortFrozenOrderAccounting", "theorem")]),
("AspisR1.OraclePortFrozenOrder.runLevel.eq_def", #[("OraclePortFrozenOrderRecoveryStep", "theorem"), ("OraclePortFrozenOrderAccounting", "theorem")]),
("AspisR1.OraclePortFrozenOrder.slotPrograms.eq_1", #[("OraclePortFrozenOrderSelectedRecovery", "theorem"), ("OraclePortFrozenOrderEnvelopes", "theorem")]),
("AspisR1.OraclePortFrozenOrder.verifyInPlace._sparseCasesOn_1.else_eq", #[("OraclePortFrozenOrderSlotPath", "theorem"), ("OraclePortFrozenOrderBounds", "theorem")]),
("AspisR1.OraclePortFrozenOrder.verifyInPlace._sparseCasesOn_2.else_eq", #[("OraclePortFrozenOrderSlotPath", "theorem"), ("OraclePortFrozenOrderBounds", "theorem")]),
("AspisR1.OraclePortFrozenOrder.verifyInPlace._sparseCasesOn_3.else_eq", #[("OraclePortFrozenOrderSlotPath", "theorem"), ("OraclePortFrozenOrderBounds", "theorem")]),
("AspisR1.OraclePortFrozenOrder.verifySlot_frozen.eq_1", #[("OraclePortFrozenOrderSlotPath", "theorem"), ("OraclePortFrozenOrderBounds", "theorem")])]
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let out ← IO.FS.Handle.mk "evidence/raw-batch-000.jsonl" .write
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
