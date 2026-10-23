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
  let requests : Array (String × Array (String × String)) := #[("AspisR1.UnifiedSampler.messageValid._sparseCasesOn_2.else_eq", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1UnifiedSamplerLaw", "theorem")]),
("AspisR1.UnifiedSampler.messageValid.eq_1", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1UnifiedSamplerLaw", "theorem")]),
("AspisR1.UnifiedSampler.messageValid.eq_2", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1UnifiedSamplerLaw", "theorem")]),
("AspisR1.UnifiedSampler.messageValid.eq_3", #[("R1LiteralSemanticMessageFacts", "theorem"), ("R1UnifiedSamplerLaw", "theorem")]),
("AspisR1.UnifiedSteps.address.eq_1", #[("R1UnifiedSemanticRecovery", "theorem"), ("R1UnifiedSemanticFacts", "theorem")]),
("AspisR1.UnifiedVerifier.verifier.congr_simp", #[("R1UnifiedSemanticCase", "theorem"), ("R1UnifiedReseedCase", "theorem"), ("R1UnifiedCanonicalProver", "theorem"), ("R1UnifiedOpeningCase", "theorem"), ("R1UnifiedQueryCase", "theorem"), ("R1UnifiedExperimentInjection", "theorem")]),
("AspisR1.childIndex.eq_1", #[("R1SecondFoldRestoration", "theorem"), ("R1RoundPairing", "theorem")]),
("AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual.eq_1", #[("ActualDecodeKFieldParserTransport", "theorem"), ("R1CandidateParserSupport", "theorem")]),
("AspisR1CandidateParser.optionDiscriminant.eq_1", #[("ActualDecodeKFieldParserTransport", "theorem"), ("R1CandidateParserSupport", "theorem")]),
("AspisR1CandidateParser.optionTag.eq_1", #[("ActualDecodeKFieldParserTransport", "theorem"), ("R1CandidateParserSupport", "theorem")]),
("AspisR1CandidateParser.optionTag.eq_2", #[("ActualDecodeKFieldParserTransport", "theorem"), ("R1CandidateParserSupport", "theorem")]),
("AspisR1PoseidonPreparedIndexProductBounds.prefixProduct.congr_simp", #[("AspisR1.PoseidonPreparedIndexLoopExactV2Fix4", "theorem"), ("AspisR1.PoseidonPreparedPrefixField", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate.eq_1", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate.eq_2", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate.eq_3", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate.eq_4", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate.eq_5", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate.eq_6", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate.eq_7", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.matchCoordinate.eq_8", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate.eq_1", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate.eq_2", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate.eq_3", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate.eq_4", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate.eq_5", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate.eq_6", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate.eq_7", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopFacts.modelCoordinate.eq_8", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopProof.sourceMask.eq_1", #[("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStepModel", "theorem"), ("AspisR1SelectedMaskProbe.ActiveMaskBasisLoopStep", "theorem")]),
("AspisR1SelectedMaskProbe.field.CM31.from_m31.eq_1", #[("OccupancyExpectedBridge", "theorem"), ("TerminalLiftM31Exact", "theorem")]),
("AspisR1SelectedMaskProbe.field.CM31.new.eq_1", #[("ExtractedMaskQmPackBase4Fragments", "theorem"), ("ExtractedMaskBasisComponents", "theorem"), ("RawPoseidonExtensionWords", "theorem")]),
("AspisR1SelectedMaskProbe.field.M31.double.eq_1", #[("ExtractedMaskQM31Mul", "theorem"), ("ExtractedMaskCM31Square", "theorem")]),
("AspisR1SelectedMaskProbe.field.QM31.from_cm31.eq_1", #[("OccupancyExpectedBridge", "theorem"), ("TerminalLiftM31Exact", "theorem")]),
("AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.lift_m31.eq_1", #[("OccupancyExpectedBridge", "theorem"), ("TerminalLiftM31Exact", "theorem")]),
("AspisR1WithdrawalCaller.pool_v1.payment_relation.validate_common.eq_1", #[("ExtractedDecoderCallerBridge", "theorem"), ("ExtractedWithdrawalCallerCarrier", "theorem")]),
("AspisV5ComponentCConcreteFoldLinearity.childIndex.eq_1", #[("R1SecondFoldRestoration", "theorem"), ("R0.RoundNormalization", "theorem")]),
("AspisV8R17.RawReducer.condSubP.eq_1", #[("ExtractedCurrentReducer", "theorem"), ("ExtractedMaskReducer", "theorem")]),
("AspisV8R17.RawReducer.foldBits.eq_1", #[("ExtractedCurrentReducer", "theorem"), ("ExtractedMaskReducer", "theorem")]),
("AspisV8R17.RawReducer.rawReduceU64.eq_1", #[("ExtractedCurrentReducer", "theorem"), ("ExtractedMaskReducer", "theorem")]),
("AspisV8R19.AdaptiveFirstReadLaw.FreshFrom.congr_simp", #[("AspisV8R19.GuardedFirstRead", "theorem"), ("CompPolyGeneralRootIndependentLaw", "theorem")]),
("AspisV8R19.OracleFiniteSupport.extend.congr_simp", #[("AspisV8R19.SamplerOracleLaws", "theorem"), ("RRFiniteRootSamplerNormalizedStateBridge", "theorem")]),
("AspisWide.FinalEncoder.exactFinalEncoder.eq_1", #[("Wide.EncoderLinearity", "theorem"), ("Wide.GRSConversion", "theorem")]),
("AspisWide.GRSConversion.exactInitialGRSConversion.eq_1", #[("Wide.Agreement", "theorem"), ("GSRuntimeInitialDistanceEncoderBridge", "theorem")]),
("AspisWide.InitialEncoder.exactInitialEncoder.eq_1", #[("Wide.FinalEncoder", "theorem"), ("Wide.EncoderConjugation", "theorem")]),
("BitVec.ofNatLT.congr_simp", #[("Init.Data.BitVec.Bootstrap", "theorem"), ("Init.Data.Range.Polymorphic.UInt", "theorem")]),
("CategoryTheory.Limits.PullbackCone.mk.congr_simp", #[("Mathlib.CategoryTheory.Limits.Shapes.RegularMono", "theorem"), ("Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc", "theorem"), ("Mathlib.CategoryTheory.Limits.Constructions.EpiMono", "theorem")]),
("CategoryTheory.Limits.PushoutCocone.mk.congr_simp", #[("Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc", "theorem"), ("Mathlib.CategoryTheory.Limits.Constructions.EpiMono", "theorem")]),
("Classical.choice.congr_simp", #[("Init.Data.Option.Lemmas", "theorem"), ("Init.While", "theorem")]),
("ClosureOperator.ofCompletePred.congr_simp", #[("Mathlib.Order.SupClosed", "theorem"), ("Mathlib.Combinatorics.Matroid.Closure", "theorem")]),
("CompPoly.CPolynomial.NTT.Domain.inverse.eq_1", #[("CompPoly.Univariate.NTT.Inverse", "theorem"), ("CompPoly.Univariate.NTT.Kernel", "theorem")]),
("CompPoly.CPolynomial.NTT.Domain.mk.congr_simp", #[("CompPoly.Univariate.NTT.Inverse", "theorem"), ("CompPoly.Univariate.NTT.Kernel", "theorem")]),
("CompPoly.CPolynomial.Raw.divModByMonicAux.eq_1", #[("ActualRawLongDivisionCost", "theorem"), ("ActualRawLongDivisionCostV4", "theorem")]),
("CompPoly.CPolynomial.Raw.divModByMonicAux.go.eq_1", #[("ActualRawLongDivisionCost", "theorem"), ("CompPoly.Univariate.DivisionCorrectness", "theorem"), ("ActualRawLongDivisionCostV4", "theorem")]),
("CompPoly.CPolynomial.Raw.divModByMonicAux.go.eq_2", #[("ActualRawLongDivisionCost", "theorem"), ("CompPoly.Univariate.DivisionCorrectness", "theorem"), ("ActualRawLongDivisionCostV4", "theorem")]),
("CompPoly.CPolynomial.Raw.leadingCoeff.eq_1", #[("ActualScaledDivisorMonic", "theorem"), ("CompPolyFactorRawDivisionBridge", "theorem")]),
("CompPoly.CPolynomial.Raw.powModBinaryAuxWith.eq_1", #[("ActualModularProductDegreeBound", "theorem"), ("ActualCompPolyPowCost", "theorem")]),
("CompPoly.CPolynomial.Raw.powModBinaryAuxWith.eq_2", #[("ActualModularProductDegreeBound", "theorem"), ("ActualCompPolyPowCost", "theorem")]),
("CompPoly.CPolynomial.Raw.powModBinaryAuxWith.eq_def", #[("ActualModularProductDegreeBound", "theorem"), ("ActualCompPolyPowCost", "theorem")]),
("CompPoly.CPolynomial.Raw.smul.eq_1", #[("ActualRawModRemainderSizeBound", "theorem"), ("ActualModularProductDegreeBound", "theorem"), ("ActualLongDivisionTotalCostV2", "theorem")]),
("CompPoly.CPolynomial.divByMonic.congr_simp", #[("CompPolyFactorRecursion", "theorem"), ("CompPoly.Bivariate.FactorMonic", "theorem"), ("CompPolyFactorSplitCount", "theorem")]),
("CompPoly.CPolynomial.gcdMonic.congr_simp", #[("CompPolySplitTrial", "theorem"), ("CompPoly.Univariate.Roots.SmoothSubgroup.Correctness", "theorem")]),
("CompPoly.CPolynomial.leadingCoeff.eq_1", #[("ActualScaledDivisorMonic", "theorem"), ("CompPolyFactorRawDivisionBridge", "theorem")]),
("CompPoly.CPolynomial.linearFactor.congr_simp", #[("CompPoly.Univariate.Roots.Correctness", "theorem"), ("CompPoly.Univariate.BatchEval.Correctness", "theorem")]),
("CompPoly.CPolynomial.modByMonic.congr_simp", #[("CompPolyPolynomialBackendBridge", "theorem"), ("CompPoly.Bivariate.FactorMonic", "theorem")]),
("CompPoly.CPolynomial.monicNormalize.congr_simp", #[("CompPolyGeneralRootsProgram", "theorem"), ("CompPoly.Univariate.Roots.RootProduct", "theorem")]),
("CompPoly.CPolynomial.monomial.congr_simp", #[("CompPoly.Univariate.ToPoly.Degree", "theorem"), ("CompPoly.Bivariate.Basic", "theorem")]),
("CompPoly.CPolynomial.natDegree.eq_1", #[("CompPolyModularRemainderDegree", "theorem"), ("CompPolyFactorRawDivisionBridge", "theorem")]),
("CompPoly.CPolynomial.ringEquiv.congr_simp", #[("CompPolySplitTrial", "theorem"), ("CompPoly.Bivariate.ToPoly", "theorem")]),
("CompPoly.DenseMatrix.freeColumns.eq_1", #[("CompPoly.LinearAlgebra.Dense.KernelCorrectness", "theorem"), ("GSDenseKernelExtractionCost", "theorem")]),
("CompPoly.DenseMatrix.homogeneousKernelBasis.eq_1", #[("CompPoly.LinearAlgebra.Dense.KernelCorrectness", "theorem"), ("CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness", "theorem")]),
("CompPoly.DenseMatrix.homogeneousWitness.eq_1", #[("CompPoly.LinearAlgebra.Dense.KernelCorrectness", "theorem"), ("CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness", "theorem")]),
("CompPoly.GuruswamiSudan.ValidInterpolationWitness.congr_simp", #[("CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness", "theorem"), ("CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness", "theorem")]),
("Con.mk.congr_simp", #[("Mathlib.GroupTheory.QuotientGroup.Defs", "theorem"), ("Mathlib.RingTheory.TwoSidedIdeal.Basic", "theorem"), ("Mathlib.GroupTheory.MonoidLocalization.Basic", "theorem")]),
("ContinuousLinearMap.mk.congr_simp", #[("Mathlib.Topology.Algebra.Module.Multilinear.Basic", "theorem"), ("Mathlib.Analysis.Calculus.Deriv.Basic", "theorem")]),
("ContinuousLinearMap.restrictScalars.congr_simp", #[("Mathlib.Analysis.Complex.Basic", "theorem"), ("Mathlib.Analysis.Calculus.Deriv.Comp", "theorem")]),
("ContinuousMultilinearMap.constOfIsEmpty.congr_simp", #[("Mathlib.Analysis.Normed.Module.Multilinear.Basic", "theorem"), ("Mathlib.Topology.Algebra.Module.Alternating.Basic", "theorem")]),
("ContinuousMultilinearMap.ofSubsingleton.congr_simp", #[("Mathlib.Analysis.Normed.Module.Multilinear.Basic", "theorem"), ("Mathlib.Topology.Algebra.Module.Alternating.Basic", "theorem")]),
("ContinuousMultilinearMap.smulRight.congr_simp", #[("Mathlib.Analysis.Normed.Module.Multilinear.Basic", "theorem"), ("Mathlib.Topology.Algebra.Module.Alternating.Basic", "theorem")]),
("CovBy.eq_1", #[("Mathlib.Order.Cover", "theorem"), ("Mathlib.Data.Prod.Lex", "theorem")]),
("DFunLike.coe.hcongr_6", #[("Mathlib.Algebra.Group.Hom.Defs", "theorem"), ("Mathlib.Logic.Equiv.Defs", "theorem")]),
("DistribMulAction.toLinearEquiv.congr_simp", #[("Mathlib.Topology.Algebra.Module.Equiv", "theorem"), ("Mathlib.LinearAlgebra.Matrix.ToLin", "theorem"), ("Mathlib.LinearAlgebra.AffineSpace.Basis", "theorem")]),
("DistribSMul.toLinearMap.congr_simp", #[("Mathlib.Algebra.Algebra.Opposite", "theorem"), ("Mathlib.Algebra.Module.Submodule.Finsupp", "theorem"), ("Mathlib.Algebra.Module.Submodule.Invariant", "theorem"), ("Mathlib.LinearAlgebra.AffineSpace.Pointwise", "theorem"), ("Mathlib.Algebra.Polynomial.HasseDeriv", "theorem")]),
("EStateM.map.eq_1", #[("Init.Control.Lawful.Instances", "theorem"), ("Init.Control.Lawful.MonadAttach.Instances", "theorem")]),
("EStateM.orElse.eq_1", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("EStateM.run.eq_1", #[("Init.Control.Lawful.Instances", "theorem"), ("Init.Control.Lawful.MonadAttach.Instances", "theorem")]),
("EStateM.tryCatch.eq_1", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("Eq.congr_simp", #[("Init.Data.Nat.Fold", "theorem"), ("Init.Data.Dyadic.Basic", "theorem")]),
("Eq.mpr.congr_simp", #[("Mathlib.Logic.Equiv.Basic", "theorem"), ("Mathlib.CategoryTheory.EqToHom", "theorem"), ("Mathlib.Combinatorics.Quiver.Push", "theorem")]),
("Eq.ndrec_symm.congr_simp", #[("Init.Grind.Ring.CommSolver", "theorem"), ("Init.Grind.Ordered.Linarith", "theorem"), ("Lean.Compiler.NameMangling", "theorem")]),
("Equiv.equivOfIsEmpty.congr_simp", #[("Mathlib.Algebra.BigOperators.Fin", "theorem"), ("Mathlib.Data.Multiset.Fintype", "theorem")]),
("Equiv.subtypeQuotientEquivQuotientSubtype.congr_simp", #[("Mathlib.Algebra.GroupWithZero.NonZeroDivisors", "theorem"), ("Mathlib.Data.Fintype.Quotient", "theorem")]),
("Equiv.subtypeUnivEquiv.congr_simp", #[("Mathlib.Algebra.BigOperators.Group.Finset.Defs", "theorem"), ("Mathlib.Order.RelIso.Set", "theorem")]),
("Except.tryCatch.eq_1", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("Except.tryCatch.eq_2", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("ExceptT.map.eq_1", #[("Init.Control.Lawful.Instances", "theorem"), ("Init.Control.Lawful.MonadAttach.Instances", "theorem")]),
("ExceptT.mk.eq_1", #[("Init.Control.Lawful.Instances", "theorem"), ("Init.Control.Lawful.MonadAttach.Instances", "theorem")]),
("ExceptT.tryCatch.eq_1", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("Exists.choose.congr_simp", #[("Init.Control.Lawful.Lemmas", "theorem"), ("Init.Data.Range.Polymorphic.UpwardEnumerable", "theorem"), ("Init.While", "theorem"), ("Std.Data.Iterators.Lemmas.Equivalence.HetT", "theorem")]),
("FS.Prefix.ext.eq_1", #[("FS.LemmaB", "theorem"), ("R1GenericNoHit", "theorem")]),
("FS.Protocol.chalAddr.eq_1", #[("FS.LemmaB", "theorem"), ("R0FS.Verifier", "theorem")])]
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let out ← IO.FS.Handle.mk "evidence/raw-batch-002.jsonl" .write
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
