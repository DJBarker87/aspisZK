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
  let requests : Array (String × Array (String × String)) := #[("R1Z.GamesR1.runLog.eq_def", #[("R1Z.RomObserverBin", "theorem"), ("R1Z.AgreeR1PBin", "theorem")]),
("R1Z.LayoutR1PBin.dLeafSalt.eq_1", #[("R1Z.RomGrammarBin", "theorem"), ("R1Z.ProverCommitSaltBytes", "theorem")]),
("R1Z.LayoutR1PBin.le64.eq_1", #[("R1Z.LayoutR1P2Bin", "theorem"), ("R1Z.RomGrammarBin", "theorem"), ("R1Z.ProverCommitSaltBytes", "theorem")]),
("R1Z.LayoutR1PBin.qLeaf.eq_1", #[("R1Z.CausalTreeOrderBin", "theorem"), ("R1Z.LayoutR1P2Bin", "theorem")]),
("R1Z.LayoutR1PBin.qNode.eq_1", #[("R1Z.CausalTreeOrderBin", "theorem"), ("R1Z.LayoutR1P2Bin", "theorem")]),
("R1Z.LayoutR1PBin.qSalt.eq_1", #[("R1Z.CausalTreeOrderBin", "theorem"), ("R1Z.LayoutR1P2Bin", "theorem")]),
("R1Z.LayoutR1PBin.rootChild.eq_1", #[("R1Z.CausalTreeOrderBin", "theorem"), ("R1Z.LayoutR1P3Bin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_1", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_10", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_11", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_12", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_13", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_14", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_2", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_3", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_4", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_5", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_6", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_7", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_8", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.PhaseScheduleBin.transcriptStage.eq_9", #[("R1Z.PhaseTranscriptBin", "theorem"), ("R1Z.PhaseMessageEncodingBin", "theorem")]),
("R1Z.ProverCommitWordCarrier.accepted.eq_1", #[("R1Z.ProverCommitSourceSuccess", "theorem"), ("R1Z.ProverCommitOwnedWord", "theorem")]),
("RRDenseCoeffVector.coeffAt.eq_1", #[("RRVectorRowBridgeV14", "theorem"), ("GSInitialMessageCandidateFilter", "theorem")]),
("RRVectorRowPolynomialBridge.vectorAt.eq_1", #[("RRConcreteState", "theorem"), ("RRConcreteChildModel", "theorem")]),
("ReaderT.run.eq_1", #[("Init.Control.Lawful.Instances", "theorem"), ("Init.Control.Lawful.MonadAttach.Instances", "theorem")]),
("RelIso.mk.congr_simp", #[("Mathlib.Order.UpperLower.CompleteLattice", "theorem"), ("Mathlib.Order.Fin.Tuple", "theorem")]),
("RingEquiv.ofBijective.congr_simp", #[("Mathlib.RingTheory.AlgebraTower", "theorem"), ("Mathlib.RingTheory.GradedAlgebra.Basic", "theorem")]),
("RingHom.mk.congr_simp", #[("Mathlib.Data.ZMod.Basic", "theorem"), ("Mathlib.Algebra.Algebra.Defs", "theorem"), ("Mathlib.GroupTheory.FreeAbelianGroup", "theorem"), ("Mathlib.Algebra.MonoidAlgebra.MapDomain", "theorem")]),
("SemilatticeInf.mk.congr_simp", #[("Mathlib.Order.Copy", "theorem"), ("Mathlib.Algebra.Order.Ring.Idempotent", "theorem")]),
("Set.EqOn.eq_1", #[("Mathlib.Data.Set.Prod", "theorem"), ("Mathlib.Algebra.Notation.Support", "theorem")]),
("Set.MapsTo.eq_1", #[("Mathlib.Data.Finset.Image", "theorem"), ("Mathlib.Order.ScottContinuity", "theorem"), ("Mathlib.Algebra.Order.Interval.Set.Monoid", "theorem"), ("Mathlib.Order.Filter.Tendsto", "theorem")]),
("Set.Nonempty.some.congr_simp", #[("Mathlib.Order.Interval.Set.OrdConnectedComponent", "theorem"), ("Mathlib.Topology.Order.LiminfLimsup", "theorem")]),
("Set.restrict.eq_1", #[("Mathlib.Data.Set.Monotone", "theorem"), ("Mathlib.Topology.Constructions", "theorem")]),
("SetLike.instMembership.hcongr_3", #[("Mathlib.Data.Fintype.Pi", "theorem"), ("Mathlib.Order.SupIndep", "theorem")]),
("Setoid.mk.congr_simp", #[("Mathlib.Data.Setoid.Basic", "theorem"), ("Mathlib.Algebra.GroupWithZero.NonZeroDivisors", "theorem")]),
("Std.DHashMap.Internal.Raw₀.alter.congr_simp", #[("Std.Data.DHashMap.Internal.Raw", "theorem"), ("Std.Data.DHashMap.Internal.Model", "theorem")]),
("Std.DHashMap.Internal.Raw₀.beq.congr_simp", #[("Std.Data.DHashMap.Internal.Raw", "theorem"), ("Std.Data.DHashMap.Internal.RawLemmas", "theorem")]),
("Std.DHashMap.Internal.Raw₀.get!.congr_simp", #[("Std.Data.DHashMap.Internal.Raw", "theorem"), ("Std.Data.DHashMap.Internal.Model", "theorem")]),
("Std.DHashMap.Internal.Raw₀.get?.congr_simp", #[("Std.Data.DHashMap.Internal.Raw", "theorem"), ("Std.Data.DHashMap.Internal.WF", "theorem")]),
("Std.DHashMap.Internal.Raw₀.getD.congr_simp", #[("Std.Data.DHashMap.Internal.Raw", "theorem"), ("Std.Data.DHashMap.Internal.Model", "theorem")]),
("Std.DHashMap.Internal.Raw₀.modify.congr_simp", #[("Std.Data.DHashMap.Internal.Raw", "theorem"), ("Std.Data.DHashMap.Internal.Model", "theorem")]),
("Std.DTreeMap.Internal.Impl.any.eq_1", #[("Std.Data.DTreeMap.Lemmas", "theorem"), ("Std.Data.DTreeMap.Raw.Lemmas", "theorem")]),
("Std.DTreeMap.Internal.Impl.ofList.eq_1", #[("Std.Data.DTreeMap.Lemmas", "theorem"), ("Std.Data.DTreeMap.Raw.Lemmas", "theorem")]),
("Std.Internal.List.beqModel.congr_simp", #[("Std.Data.DHashMap.Internal.RawLemmas", "theorem"), ("Std.Data.DTreeMap.Internal.Lemmas", "theorem")]),
("Std.Iter.step.eq_1", #[("Init.Data.Range.Polymorphic.RangeIterator", "theorem"), ("Init.Data.Iterators.Lemmas.Consumers.Collect", "theorem"), ("Init.Data.Iterators.Lemmas.Combinators.FlatMap", "theorem")]),
("Std.Iter.toArray.eq_1", #[("Init.Data.Iterators.Lemmas.Combinators.FlatMap", "theorem"), ("Std.Data.Iterators.Lemmas.Producers.Array", "theorem")]),
("Std.Iter.toIterM.eq_1", #[("Init.Data.Range.Polymorphic.RangeIterator", "theorem"), ("Init.Data.String.Lemmas.Pattern.Basic", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Zip", "theorem"), ("Std.Data.Iterators.Lemmas.Producers.Repeat", "theorem")]),
("Std.Iter.toList.eq_1", #[("Init.Data.Iterators.Lemmas.Combinators.FlatMap", "theorem"), ("Std.Data.Iterators.Lemmas.Producers.Array", "theorem")]),
("Std.IterM.Equiv.congr_simp", #[("Std.Data.Iterators.Lemmas.Consumers.Monadic.Collect", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap", "theorem")]),
("Std.IterM.IsPlausibleSkipSuccessorOf.eq_1", #[("Init.Data.Range.Polymorphic.RangeIterator", "theorem"), ("Std.Data.Iterators.Combinators.Monadic.StepSize", "theorem"), ("Std.Data.Iterators.Combinators.Monadic.Drop", "theorem")]),
("Std.IterM.Step.toPure.eq_1", #[("Init.Data.Range.Polymorphic.RangeIterator", "theorem"), ("Init.Data.Iterators.Lemmas.Consumers.Loop", "theorem")]),
("Std.IterM.finitelyManySkips.congr_simp", #[("Init.Data.Iterators.Combinators.Monadic.Take", "theorem"), ("Init.Data.Iterators.Combinators.Monadic.Attach", "theorem"), ("Std.Data.Iterators.Combinators.Monadic.StepSize", "theorem")]),
("Std.IterM.finitelyManySteps.congr_simp", #[("Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect", "theorem"), ("Init.Data.Iterators.Combinators.Monadic.Take", "theorem"), ("Init.Data.Iterators.Combinators.Monadic.Attach", "theorem"), ("Std.Data.Iterators.Combinators.Monadic.StepSize", "theorem")]),
("Std.IterM.step.eq_1", #[("Init.Data.Range.Polymorphic.RangeIterator", "theorem"), ("Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap", "theorem"), ("Init.Data.Iterators.Lemmas.Combinators.Monadic.Take", "theorem"), ("Init.Data.Iterators.Lemmas.Producers.Monadic.List", "theorem"), ("Init.Data.Iterators.Lemmas.Combinators.Monadic.Append", "theorem"), ("Init.Data.Iterators.Lemmas.Combinators.Monadic.ULift", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.TakeWhile", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.Drop", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.DropWhile", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip", "theorem"), ("Std.Data.DTreeMap.Internal.Zipper", "theorem")]),
("Std.IterM.toIter.eq_1", #[("Init.Data.String.Lemmas.Pattern.Basic", "theorem"), ("Init.Data.Iterators.Lemmas.Producers.List", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Zip", "theorem"), ("Std.Data.Iterators.Lemmas.Producers.Repeat", "theorem")]),
("Std.IterStep.bundledQuotient.eq_1", #[("Std.Data.Iterators.Lemmas.Consumers.Monadic.Collect", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap", "theorem")]),
("Std.Legacy.Range.mk.congr_simp", #[("Aeneas.Data.Range.Lemmas", "theorem"), ("CompPoly.Univariate.NTT.Transform", "theorem"), ("CompPoly.LinearAlgebra.Dense.RowOpsCorrectness", "theorem")]),
("Std.PRange.UpwardEnumerable.LE.eq_1", #[("Init.Data.Range.Polymorphic.Map", "theorem"), ("Init.Data.Range.Polymorphic.Fin", "theorem"), ("Init.Data.Range.Polymorphic.Int", "theorem"), ("Init.Data.Range.Polymorphic.BitVec", "theorem")]),
("Std.PRange.UpwardEnumerable.LT.eq_1", #[("Init.Data.Range.Polymorphic.Map", "theorem"), ("Init.Data.Range.Polymorphic.Fin", "theorem"), ("Init.Data.Range.Polymorphic.Int", "theorem"), ("Init.Data.Range.Polymorphic.BitVec", "theorem")]),
("Std.PlausibleIterStep.yield.congr_simp", #[("Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap", "theorem"), ("Init.Data.Iterators.Lemmas.Combinators.Monadic.Take", "theorem"), ("Init.Data.Iterators.Lemmas.Combinators.Monadic.Append", "theorem"), ("Init.Data.Iterators.Lemmas.Combinators.Monadic.ULift", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.TakeWhile", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.Drop", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.DropWhile", "theorem"), ("Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip", "theorem"), ("Std.Data.Iterators.Lemmas.Producers.Monadic.Array", "theorem")]),
("Std.Slice.size.eq_1", #[("Init.Data.Array.Subarray", "theorem"), ("Init.Data.Slice.InternalLemmas", "theorem")]),
("StrictAnti.eq_1", #[("Mathlib.Data.Set.Order", "theorem"), ("Mathlib.Data.List.Sort", "theorem")]),
("StrictMono.eq_1", #[("Mathlib.Order.WithBot", "theorem"), ("Mathlib.Data.Set.Order", "theorem"), ("Mathlib.Data.List.Sort", "theorem"), ("Mathlib.Data.Set.Monotone", "theorem")]),
("StrictMonoOn.eq_1", #[("Mathlib.Data.Set.Order", "theorem"), ("Mathlib.Data.Set.Monotone", "theorem")]),
("String.Pos.Raw.atEnd.eq_1", #[("Init.Data.String.Iterator", "theorem"), ("Lean.Parser.Types", "theorem")]),
("String.Pos.byte.congr_simp", #[("Init.Data.String.Lemmas.Basic", "theorem"), ("Init.Data.String.Modify", "theorem")]),
("String.Slice.Pattern.Internal.memcmpSlice.congr_simp", #[("Init.Data.String.Lemmas.Slice", "theorem"), ("Init.Data.String.Lemmas.Pattern.String.ForwardPattern", "theorem")]),
("String.Slice.Pattern.Model.split._unary.induct_unfolding", #[("Init.Data.String.Lemmas.Pattern.Split.Char", "theorem"), ("Init.Data.String.Lemmas.Pattern.Split.Pred", "theorem")]),
("String.Slice.Pattern.Model.split.induct_unfolding", #[("Init.Data.String.Lemmas.Pattern.Split.Char", "theorem"), ("Init.Data.String.Lemmas.Pattern.Split.Pred", "theorem")]),
("String.Slice.Pos.revSkipWhile._unary.induct_unfolding", #[("Init.Data.String.Lemmas.Pattern.Pred", "theorem"), ("Init.Data.String.Lemmas.Pattern.Char", "theorem"), ("Init.Data.String.Lemmas.Pattern.String.ForwardPattern", "theorem"), ("Init.Data.String.Lemmas.Pattern.TakeDrop.Basic", "theorem")]),
("String.Slice.Pos.revSkipWhile.induct_unfolding", #[("Init.Data.String.Lemmas.Pattern.Pred", "theorem"), ("Init.Data.String.Lemmas.Pattern.Char", "theorem"), ("Init.Data.String.Lemmas.Pattern.String.ForwardPattern", "theorem"), ("Init.Data.String.Lemmas.Pattern.TakeDrop.Basic", "theorem")]),
("String.Slice.Pos.skipWhile._unary.induct_unfolding", #[("Init.Data.String.Lemmas.Pattern.Pred", "theorem"), ("Init.Data.String.Lemmas.Pattern.Char", "theorem"), ("Init.Data.String.Lemmas.Pattern.String.ForwardPattern", "theorem"), ("Init.Data.String.Lemmas.Pattern.TakeDrop.Basic", "theorem")]),
("String.Slice.Pos.skipWhile.induct_unfolding", #[("Init.Data.String.Lemmas.Pattern.Pred", "theorem"), ("Init.Data.String.Lemmas.Pattern.Char", "theorem"), ("Init.Data.String.Lemmas.Pattern.String.ForwardPattern", "theorem"), ("Init.Data.String.Lemmas.Pattern.TakeDrop.Basic", "theorem")]),
("String.pos.congr_simp", #[("Init.Data.String.Search", "theorem"), ("Init.Data.String.Lemmas.Basic", "theorem"), ("Init.Data.String.Substring", "theorem")]),
("String.rawEndPos.eq_1", #[("Init.Data.String.Iterator", "theorem"), ("Lean.Parser.Types", "theorem")]),
("String.utf8EncodeChar.eq_def", #[("Init.Data.String.Decode", "theorem"), ("Init.Data.String.Defs", "theorem")]),
("String.utf8EncodeChar.fun_cases_unfolding", #[("Init.Data.String.Decode", "theorem"), ("Init.Data.String.Defs", "theorem")]),
("Subalgebra.copy.congr_simp", #[("Mathlib.Algebra.Star.Subalgebra", "theorem"), ("Mathlib.RingTheory.Localization.AsSubring", "theorem")]),
("Subalgebra.equivOfEq.congr_simp", #[("Mathlib.Algebra.MvPolynomial.Supported", "theorem"), ("Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed", "theorem")]),
("Subalgebra.inclusion.congr_simp", #[("Mathlib.Algebra.Algebra.Subalgebra.Directed", "theorem"), ("Mathlib.RingTheory.AlgebraicIndependent.Transcendental", "theorem")]),
("Submodule.mk.congr_simp", #[("Mathlib.Algebra.Module.Submodule.Lattice", "theorem"), ("Mathlib.GroupTheory.Torsion", "theorem")]),
("Subring.mk.congr_simp", #[("Mathlib.FieldTheory.Fixed", "theorem"), ("Mathlib.FieldTheory.IntermediateField.Adjoin.Defs", "theorem"), ("Mathlib.Topology.Algebra.Valued.ValuationTopology", "theorem")]),
("Subsemiring.mk.congr_simp", #[("Mathlib.Algebra.Star.Subalgebra", "theorem"), ("Mathlib.FieldTheory.Fixed", "theorem"), ("Mathlib.Topology.Algebra.Valued.ValuationTopology", "theorem")]),
("Subtype.map.congr_simp", #[("Mathlib.Data.Set.Image", "theorem"), ("Mathlib.Data.List.Basic", "theorem")]),
("Subtype.map.eq_1", #[("Mathlib.Data.Set.Image", "theorem"), ("Mathlib.Data.List.Basic", "theorem")]),
("SupHom.mk.congr_simp", #[("Mathlib.Order.Sublattice", "theorem"), ("Mathlib.Order.Category.Lat", "theorem")]),
("Trunc.lift.congr_simp", #[("Mathlib.Data.DFinsupp.BigOperators", "theorem"), ("Mathlib.Algebra.Order.Antidiag.Pi", "theorem")]),
("UInt16.toNat.eq_1", #[("Init.Data.UInt.Lemmas", "theorem"), ("Init.SizeOfLemmas", "theorem")]),
("UInt32.toNat.eq_1", #[("Init.Data.UInt.Lemmas", "theorem"), ("Init.SizeOfLemmas", "theorem")]),
("UInt64.toNat.eq_1", #[("Init.Data.UInt.Lemmas", "theorem"), ("Init.SizeOfLemmas", "theorem")]),
("UInt8.toNat.eq_1", #[("Init.Data.UInt.Lemmas", "theorem"), ("Init.SizeOfLemmas", "theorem")]),
("USize.toNat.eq_1", #[("Init.Data.UInt.Lemmas", "theorem"), ("Init.SizeOfLemmas", "theorem")]),
("Vector.swap.congr_simp", #[("Init.Data.Vector.Lemmas", "theorem"), ("Init.Data.Array.QSort.Basic", "theorem")]),
("WellFounded.extrinsicFix₂.congr_simp", #[("Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect", "theorem"), ("Init.Data.Iterators.Consumers.Access", "theorem")]),
("ZMod.castHom.congr_simp", #[("Mathlib.FieldTheory.Finite.Basic", "theorem"), ("Mathlib.Data.ZMod.Units", "theorem")]),
("ZeroHom.mk.congr_simp", #[("Mathlib.Algebra.Group.Equiv.TypeTags", "theorem"), ("Mathlib.Algebra.BigOperators.Finsupp.Basic", "theorem"), ("Mathlib.Analysis.Normed.Group.Seminorm", "theorem"), ("Mathlib.Data.DFinsupp.BigOperators", "theorem"), ("Mathlib.Algebra.Group.AddChar", "theorem"), ("Mathlib.Data.Int.WithZero", "theorem")]),
("_private.Init.Data.Array.Basic.0.Array.findSomeRevM?.find.congr_simp", #[("Init.Data.List.ToArray", "theorem"), ("Init.Internal.Order.Lemmas", "theorem")]),
("_private.Init.Data.Array.Basic.0.Array.ofFn.go.congr_simp", #[("Init.Data.Array.Lemmas", "theorem"), ("Init.Data.Array.OfFn", "theorem")]),
("_private.Init.Data.String.Slice.0.String.Slice.Pos.skipWhile.match_1.congr_eq_1", #[("Init.Data.String.Lemmas.Pattern.Pred", "theorem"), ("Init.Data.String.Lemmas.Pattern.TakeDrop.Basic", "theorem")]),
("_private.Init.Data.String.Slice.0.String.Slice.Pos.skipWhile.match_1.congr_eq_2", #[("Init.Data.String.Lemmas.Pattern.Pred", "theorem"), ("Init.Data.String.Lemmas.Pattern.TakeDrop.Basic", "theorem")])]
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let out ← IO.FS.Handle.mk "evidence/raw-batch-005.jsonl" .write
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
