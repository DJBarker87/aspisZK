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
  let requests : Array (String × Array (String × String)) := #[("MonoidWithZeroHom.ofClass.congr_simp", #[("Mathlib.Data.Rat.Cast.Defs", "theorem"), ("Mathlib.Algebra.GroupWithZero.Range", "theorem")]),
("MonotoneOn.eq_1", #[("Mathlib.Data.Set.Order", "theorem"), ("Mathlib.Data.Set.Monotone", "theorem")]),
("MulEquiv.mk.congr_simp", #[("Mathlib.Algebra.GroupWithZero.WithZero", "theorem"), ("Mathlib.Algebra.Ring.Equiv", "theorem"), ("Mathlib.Algebra.Group.End", "theorem")]),
("MulEquiv.ofBijective.congr_simp", #[("Mathlib.GroupTheory.SpecificGroups.Cyclic", "theorem"), ("Mathlib.Topology.Algebra.Valued.ValuedField", "theorem")]),
("MulEquivClass.toMulEquiv.congr_simp", #[("Mathlib.Algebra.Order.Hom.Monoid", "theorem"), ("Mathlib.GroupTheory.Submonoid.Center", "theorem"), ("Mathlib.Algebra.Ring.Divisibility.Basic", "theorem"), ("Mathlib.GroupTheory.MonoidLocalization.Basic", "theorem")]),
("Multiset.pmap.congr_simp", #[("Mathlib.Data.Fintype.EquivFin", "theorem"), ("Mathlib.Data.Finset.Powerset", "theorem")]),
("MvPolynomial.renameEquiv.eq_1", #[("Mathlib.RingTheory.Polynomial.Basic", "theorem"), ("Mathlib.RingTheory.TensorProduct.MvPolynomial", "theorem")]),
("Nat.castEmbedding.congr_simp", #[("Mathlib.NumberTheory.Divisors", "theorem"), ("Mathlib.Data.Int.Interval", "theorem"), ("Mathlib.Algebra.Polynomial.Laurent", "theorem")]),
("Nat.factorial.eq_1", #[("Mathlib.Data.List.Permutation", "theorem"), ("Mathlib.Analysis.Complex.Exponential", "theorem"), ("Mathlib.Data.Nat.Factorial.BigOperators", "theorem"), ("Mathlib.Data.Nat.Multiplicity", "theorem"), ("Mathlib.Data.Nat.Factorial.SuperFactorial", "theorem"), ("Mathlib.Data.Nat.Factorial.DoubleFactorial", "theorem")]),
("Nat.factorial.eq_2", #[("Mathlib.Data.List.Permutation", "theorem"), ("Mathlib.Analysis.Complex.Exponential", "theorem"), ("Mathlib.Data.Nat.Factorial.BigOperators", "theorem"), ("Mathlib.Data.Nat.Multiplicity", "theorem"), ("Mathlib.Data.Nat.Factorial.SuperFactorial", "theorem"), ("Mathlib.Data.Nat.Factorial.DoubleFactorial", "theorem")]),
("Nat.factorial.eq_def", #[("Mathlib.Data.List.Permutation", "theorem"), ("Mathlib.Analysis.Complex.Exponential", "theorem"), ("Mathlib.Data.Nat.Factorial.BigOperators", "theorem"), ("Mathlib.Data.Nat.Multiplicity", "theorem"), ("Mathlib.Data.Nat.Factorial.SuperFactorial", "theorem"), ("Mathlib.Data.Nat.Factorial.DoubleFactorial", "theorem")]),
("Nat.lt_wfRel.eq_1", #[("Init.Data.String.Pattern.Basic", "theorem"), ("Init.Data.Range.Polymorphic.RangeIterator", "theorem"), ("Init.Data.String.Iterate", "theorem"), ("Init.Data.Iterators.Consumers.Access", "theorem"), ("Init.Data.Iterators.Combinators.Monadic.Attach", "theorem")]),
("Nat.mod_lt._simp_1", #[("Aeneas.Tactic.Simp.SimpScalar.SimpScalar", "theorem"), ("Aeneas.Tactic.Conv.ZModify.ZModify", "theorem")]),
("Nat.repeat.eq_1", #[("Init.Data.String.Length", "theorem"), ("Std.Data.Iterators.Lemmas.Producers.Repeat", "theorem")]),
("Nat.repeat.eq_2", #[("Init.Data.String.Length", "theorem"), ("Std.Data.Iterators.Lemmas.Producers.Repeat", "theorem")]),
("Nat.repeat.eq_def", #[("Init.Data.String.Length", "theorem"), ("Std.Data.Iterators.Lemmas.Producers.Repeat", "theorem")]),
("Ne.eq_1", #[("Init.Data.Int.Lemmas", "theorem"), ("Lean.Elab.Tactic.Omega.MinNatAbs", "theorem")]),
("Ne.eq_def", #[("Mathlib.Order.Basic", "theorem"), ("Mathlib.Data.List.Nodup", "theorem"), ("Mathlib.Data.Seq.Defs", "theorem")]),
("NonUnitalAlgHom.comp.congr_simp", #[("Mathlib.Algebra.Algebra.NonUnitalSubalgebra", "theorem"), ("Mathlib.Algebra.Star.StarAlgHom", "theorem")]),
("Nonempty.some.congr_simp", #[("Mathlib.Order.RelSeries", "theorem"), ("Mathlib.Order.SuccPred.LinearLocallyFinite", "theorem"), ("Mathlib.CategoryTheory.Skeletal", "theorem")]),
("Normal.algHomEquivAut.eq_1", #[("Mathlib.RingTheory.Trace.Basic", "theorem"), ("Mathlib.RingTheory.Norm.Transitivity", "theorem")]),
("OneHom.mk.congr_simp", #[("Mathlib.Algebra.Group.Units.Equiv", "theorem"), ("Mathlib.Algebra.Group.Equiv.TypeTags", "theorem"), ("Mathlib.Algebra.FreeMonoid.Basic", "theorem"), ("Mathlib.Algebra.Algebra.Defs", "theorem"), ("Mathlib.Algebra.Group.Graph", "theorem"), ("Mathlib.Topology.Algebra.Constructions", "theorem"), ("Mathlib.GroupTheory.MonoidLocalization.Basic", "theorem")]),
("Option.get.hcongr_3", #[("Std.Http.Internal.IndexMultiMap", "theorem"), ("Mathlib.Data.Sum.Basic", "theorem")]),
("Option.guard.eq_1", #[("Init.Data.Option.Lemmas", "theorem"), ("Init.Data.List.Erase", "theorem")]),
("Option.isSome.eq_1", #[("Init.Data.Option.Lemmas", "theorem"), ("Init.Data.AC", "theorem")]),
("Option.isSome.eq_2", #[("Init.Data.Option.Lemmas", "theorem"), ("Init.Data.AC", "theorem")]),
("Option.merge.eq_1", #[("Init.Omega.Constraint", "theorem"), ("Init.Data.Option.Lemmas", "theorem")]),
("Option.merge.eq_2", #[("Init.Omega.Constraint", "theorem"), ("Init.Data.Option.Lemmas", "theorem")]),
("Option.merge.eq_3", #[("Init.Omega.Constraint", "theorem"), ("Init.Data.Option.Lemmas", "theorem")]),
("Option.merge.eq_4", #[("Init.Omega.Constraint", "theorem"), ("Init.Data.Option.Lemmas", "theorem")]),
("Option.orElse.eq_1", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("Option.orElse.eq_2", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("Option.toList.eq_1", #[("Init.Data.List.TakeDrop", "theorem"), ("Init.Data.Option.Attach", "theorem")]),
("Option.toList.eq_2", #[("Init.Data.List.TakeDrop", "theorem"), ("Init.Data.Option.Attach", "theorem")]),
("Option.tryCatch.eq_1", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("Option.tryCatch.eq_2", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("OptionT.tryCatch.eq_1", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("OrderEmbedding.ofMapLEIff.congr_simp", #[("Mathlib.Data.List.NodupEquivFin", "theorem"), ("Mathlib.Data.Finset.Option", "theorem")]),
("OrderIso.symm.eq_1", #[("Mathlib.Data.Fintype.Fin", "theorem"), ("Mathlib.Order.Fin.Tuple", "theorem")]),
("OrderMonoidIso.mk.congr_simp", #[("Mathlib.Algebra.Order.Hom.MonoidWithZero", "theorem"), ("Mathlib.Algebra.Order.Hom.TypeTags", "theorem")]),
("PLift.up.congr_simp", #[("Mathlib.Data.Fintype.Basic", "theorem"), ("Mathlib.CategoryTheory.Discrete.Basic", "theorem")]),
("Prod.swap.eq_1", #[("Mathlib.NumberTheory.Divisors", "theorem"), ("Mathlib.Order.Filter.Prod", "theorem"), ("Mathlib.LinearAlgebra.LinearPMap", "theorem"), ("Mathlib.Order.GameAdd", "theorem")]),
("Quot.lift.congr_simp", #[("Init.Grind.Ring.Envelope", "theorem"), ("Init.Grind.Module.Envelope", "theorem"), ("Std.Data.Iterators.Lemmas.Equivalence.StepCongr", "theorem")]),
("Quot.map.congr_simp", #[("Mathlib.GroupTheory.FreeGroup.Basic", "theorem"), ("Mathlib.Data.Sym.Sym2", "theorem"), ("Mathlib.CategoryTheory.IsomorphismClasses", "theorem")]),
("Quotient.lift.congr_simp", #[("Std.Data.ExtDHashMap.Lemmas", "theorem"), ("Mathlib.GroupTheory.Coset.Basic", "theorem"), ("Mathlib.Topology.Connected.Clopen", "theorem")]),
("Quotient.mk.eq_1", #[("Std.Data.ExtDHashMap.Lemmas", "theorem"), ("Std.Data.ExtDTreeMap.Lemmas", "theorem"), ("Mathlib.Data.Setoid.Basic", "theorem")]),
("QuotientAddGroup.lift.congr_simp", #[("Mathlib.Analysis.Normed.Group.Quotient", "theorem"), ("Mathlib.Algebra.Polynomial.Bivariate", "theorem")]),
("R0C.V3.OrderOK.eq_1", #[("R1InitialTrace", "theorem"), ("R1QueryOwnFollow", "theorem"), ("R1ReseedOwnFollow", "theorem"), ("R1ReseedTrace", "theorem")]),
("R0C.V3.OrderOK.eq_2", #[("R1InitialTrace", "theorem"), ("R1QueryOwnFollow", "theorem"), ("R1ReseedOwnFollow", "theorem"), ("R1ReseedTrace", "theorem")]),
("R0C.V3.OrderOK.eq_def", #[("R1InitialTrace", "theorem"), ("R1QueryOwnFollow", "theorem"), ("R1ReseedOwnFollow", "theorem"), ("R1ReseedTrace", "theorem")]),
("R0C.V3.answers.eq_1", #[("R0C.V3.BSOk", "theorem"), ("BackgroundAddressMap", "theorem")]),
("R0P.Mask.maskOnlyFactorExponent.eq_1", #[("R0Z.PureRounds", "theorem"), ("ExtractedMaskSemanticBridge", "theorem")]),
("R0P.Mask.semPolysZ.eq_1", #[("R1SemanticPayloadView", "theorem"), ("R0P.MaskPrefix", "theorem")]),
("R0P.Mask.semanticBadZ._sparseCasesOn_2.else_eq", #[("R0P.MaskDensity", "theorem"), ("R0P.MaskNoHit", "theorem")]),
("R0P.Mask.towerBasis.eq_1", #[("ExtractedMaskQmPackBase4Semantic", "theorem"), ("PoseidonCandidateScalarResidualWideV5", "theorem")]),
("R0P.SemSource.eqValue.eq_1", #[("R0P.SemHonest", "theorem"), ("EqualityValueProduct", "theorem")]),
("R0P.SemSource.selAt.eq_1", #[("R0P.SemHonest", "theorem"), ("R0P.SemDeg", "theorem")]),
("R0P.SemSource.succCarry.eq_1", #[("R0P.SemHonest", "theorem"), ("R0P.SemDeg", "theorem")]),
("R0P.SemSource.succCarry.eq_2", #[("R0P.SemHonest", "theorem"), ("R0P.SemDeg", "theorem")]),
("R0P.SemSource.succCarry.eq_def", #[("R0P.SemHonest", "theorem"), ("R0P.SemDeg", "theorem")]),
("R0P.SemSource.toR0.eq_1", #[("R0P.SemHonest", "theorem"), ("R0P.SemDeg", "theorem")]),
("R0P.SemSource.virtualPoly.eq_1", #[("R0P.SemAccept", "theorem"), ("R0P.SemHonest", "theorem")]),
("R0P.absorb.eq_1", #[("R0P.Extraction", "theorem"), ("R1OutputNotes", "theorem"), ("R1NoteHashMap", "theorem")]),
("R0P.assetFamily.eq_1", #[("R0P.LaneMap", "theorem"), ("AssetFamilyFieldTransport", "theorem")]),
("R0P.assetScalarLanes.eq_1", #[("R0P.LaneMap", "theorem"), ("AssetFamilyFieldTransport", "theorem")]),
("R0P.assetScalarLanes.eq_2", #[("R0P.LaneMap", "theorem"), ("AssetFamilyFieldTransport", "theorem")]),
("R0P.copyEvaluateWithSelectors.eq_1", #[("R0P.SemDegFamilies", "theorem"), ("AspisR1.CopyEvaluatorModel", "theorem")]),
("R0P.copyPattern11.eq_1", #[("R1PairCopyLinks", "theorem"), ("R1InputPairCopyLinks", "theorem")]),
("R0P.digestFamily.eq_1", #[("R0P.LaneMap", "theorem"), ("DigestFamilyFieldTransport", "theorem")]),
("R0P.digestOf.eq_1", #[("R0P.Extraction", "theorem"), ("R1OutputNotes", "theorem")]),
("R0P.g2High.eq_1", #[("R0P.SemDeg", "theorem"), ("PathFamilyFieldTransport", "theorem")]),
("R0P.g2Low.eq_1", #[("R0P.SemDeg", "theorem"), ("PathFamilyFieldTransport", "theorem")]),
("R0P.merkleRootAux.eq_1", #[("R0P.Extraction", "theorem"), ("R1Z.BuilderSemanticBridge", "theorem")]),
("R0P.merkleRootAux.eq_2", #[("R0P.Extraction", "theorem"), ("R1Z.BuilderSemanticBridge", "theorem")]),
("R0P.merkleRootAux.eq_def", #[("R0P.Extraction", "theorem"), ("R1NoteHashMap", "theorem"), ("R1Z.BuilderSemanticBridge", "theorem")]),
("R0P.merkleStep.eq_1", #[("R0P.Extraction", "theorem"), ("R1NoteHashMap", "theorem"), ("R1Z.BuilderSemanticBridge", "theorem")]),
("R0P.pathFamily.eq_1", #[("R0P.LaneMap", "theorem"), ("PathFamilyFieldTransport", "theorem")]),
("R0P.poseidonInternalLinear.eq_1", #[("R0P.SemDegFamilies", "theorem"), ("PoseidonInternalLinearExact", "theorem")]),
("R0P.poseidonMat4.eq_1", #[("R0P.SemDegFamilies", "theorem"), ("PoseidonMap", "theorem"), ("RawPoseidonExternalRows", "theorem")]),
("R0P.poseidonPackingFormula.eq_1", #[("AspisR1.PoseidonResidualPacking", "theorem"), ("PoseidonResidualFieldTransport", "theorem"), ("PoseidonExternalPackedModel", "theorem")]),
("R0P.rowOpenings.eq_1", #[("R0P.Path", "theorem"), ("R0P.Value", "theorem"), ("R0P.Positive", "theorem"), ("R0P.Occupancy", "theorem"), ("R0P.Asset", "theorem")]),
("R0P.spongeInit.eq_1", #[("R0P.Extraction", "theorem"), ("R1OutputNotes", "theorem"), ("R1NoteHashMap", "theorem"), ("R1Z.BuilderSemanticBridge", "theorem")]),
("R0P.succRow.eq_1", #[("R0P.Poseidon", "theorem"), ("R0P.Value", "theorem"), ("R0P.Positive", "theorem")]),
("R0P.tracePath.eq_1", #[("R0P.Extraction", "theorem"), ("R1InputPair", "theorem")]),
("R0P.valueFamily.eq_1", #[("R0P.LaneMap", "theorem"), ("ValueFamilyFieldTransport", "theorem")]),
("R0P.valueReconstruct10.eq_1", #[("R0Z.TerminalEligible", "theorem"), ("ValueFamilyFieldTransport", "theorem")]),
("R0WriterCopies.m31_sub.eq_1", #[("R0Z.NodeRefine", "theorem"), ("R0Z.WriterRefineValueModel", "theorem")]),
("R0Z.BuilderModel.appCur.eq_1", #[("R0Z.BuilderModelDigest", "theorem"), ("R0Z.BuilderModelBase", "theorem")]),
("R0Z.BuilderModel.appCur.eq_2", #[("R0Z.BuilderModelDigest", "theorem"), ("R0Z.BuilderModelBase", "theorem")]),
("R0Z.BuilderModel.appCur.eq_def", #[("R0Z.BuilderModelDigest", "theorem"), ("R0Z.BuilderModelBase", "theorem")]),
("R0Z.BuilderModel.buildModel.eq_1", #[("R0Z.BuilderModelAux", "theorem"), ("R0Z.BuilderModelHash", "theorem")]),
("R0Z.BuilderModel.ordered.eq_1", #[("R0Z.BuilderModelAux", "theorem"), ("R1Z.BuilderSemanticBridge", "theorem")]),
("R0Z.BuilderModel.treeCur.eq_1", #[("R0Z.BuilderModelDigest", "theorem"), ("R0Z.BuilderModelBase", "theorem"), ("R1Z.BuilderSemanticBridge", "theorem")]),
("R0Z.BuilderModel.treeCur.eq_2", #[("R0Z.BuilderModelDigest", "theorem"), ("R0Z.BuilderModelBase", "theorem"), ("R1Z.BuilderSemanticBridge", "theorem")]),
("R0Z.BuilderModel.treeCur.eq_def", #[("R0Z.BuilderModelDigest", "theorem"), ("R0Z.BuilderModelBase", "theorem"), ("R1Z.BuilderSemanticBridge", "theorem")]),
("R0Z.FsAbort.eventMass.eq_1", #[("R1Z.ProverCommitSimulatorSeedGuess18", "theorem"), ("R1Z.BuilderExecutionBoundary", "theorem")]),
("R0Z.HonestView.prepare.eq_1", #[("R0Z.JointTrace", "theorem"), ("R0Z.TerminalEligible", "theorem")]),
("R1Z.GamesR1.runLog.eq_1", #[("R1Z.RomObserverBin", "theorem"), ("R1Z.AgreeR1PBin", "theorem")]),
("R1Z.GamesR1.runLog.eq_2", #[("R1Z.RomObserverBin", "theorem"), ("R1Z.AgreeR1PBin", "theorem")]),
("R1Z.GamesR1.runLog.eq_3", #[("R1Z.RomObserverBin", "theorem"), ("R1Z.AgreeR1PBin", "theorem")])]
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let out ← IO.FS.Handle.mk "evidence/raw-batch-004.jsonl" .write
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
