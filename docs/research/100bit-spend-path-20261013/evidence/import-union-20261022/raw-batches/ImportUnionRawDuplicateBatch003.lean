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
  let requests : Array (String × Array (String × String)) := #[("FS2.Duplex.Params.mk.congr_simp", #[("R1LiteralTranscript", "theorem"), ("R1SelectedIndexedRead", "theorem")]),
("FS2.Protocol.chal.congr_simp", #[("FS2.DuplexWalk", "theorem"), ("LiteralAdaptiveClassifierHitToDecodedChain", "theorem"), ("StartChargeHit", "theorem")]),
("FS2.Protocol.transcript.congr_simp", #[("FS2.Theorem", "theorem"), ("R1GenericNoHitFS2", "theorem")]),
("FS2.Sampler.multi.congr_simp", #[("FS2.LemmaA", "theorem"), ("R0C.QuerySampler", "theorem"), ("R1ProgramSamplerMap", "theorem")]),
("FS2.Sampler.toProgram.eq_1", #[("FS2.LemmaA", "theorem"), ("R0C.QuerySampler", "theorem"), ("R1ProgramSamplerMap", "theorem")]),
("FS2.Sampler.toProgram.eq_2", #[("FS2.LemmaA", "theorem"), ("R0C.QuerySampler", "theorem"), ("R1ProgramSamplerMap", "theorem")]),
("FS2.Sampler.toProgram.eq_3", #[("FS2.LemmaA", "theorem"), ("R0C.QuerySampler", "theorem"), ("R1ProgramSamplerMap", "theorem")]),
("FS2.Sampler.toProgram.eq_def", #[("FS2.LemmaA", "theorem"), ("R0C.QuerySampler", "theorem"), ("R1ProgramSamplerMap", "theorem")]),
("False.elim.congr_simp", #[("Init.Data.Fin.Lemmas", "theorem"), ("Init.Data.String.Basic", "theorem"), ("Std.Data.DTreeMap.Internal.Balancing", "theorem")]),
("Filter.Tendsto.eq_1", #[("Mathlib.Order.Filter.Bases.Basic", "theorem"), ("Mathlib.Order.Filter.Tendsto", "theorem"), ("Mathlib.Topology.Basic", "theorem")]),
("Filter.pi.eq_1", #[("Mathlib.Order.Filter.Ker", "theorem"), ("Mathlib.Order.Filter.Pi", "theorem")]),
("Fin.castAdd.eq_1", #[("R0P.Schedule", "theorem"), ("R0P.Digest", "theorem")]),
("Fin.castLE.eq_1", #[("R0P.Schedule", "theorem"), ("R0P.Digest", "theorem")]),
("Fin.mk.hcongr_3", #[("Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult", "theorem"), ("Mathlib.Data.List.Basic", "theorem"), ("Mathlib.Data.Fin.Tuple.Basic", "theorem"), ("Batteries.Data.BitVec.Lemmas", "theorem")]),
("Fin.subNat.eq_1", #[("Mathlib.Order.RelSeries", "theorem"), ("Mathlib.GroupTheory.Perm.Fin", "theorem")]),
("Fin.succ.eq_1", #[("Batteries.Data.BitVec.Lemmas", "theorem"), ("R1SamplerBlockRank", "theorem"), ("Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno", "theorem")]),
("Fin.val.hcongr_2", #[("Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult", "theorem"), ("Mathlib.Data.Fin.SuccPred", "theorem"), ("Batteries.Data.List.Count", "theorem")]),
("Finset.image.eq_1", #[("Mathlib.Data.Finset.Card", "theorem"), ("Mathlib.Data.Fintype.Basic", "theorem")]),
("Finset.instSetLike.hcongr_1", #[("Mathlib.Data.Fintype.Pi", "theorem"), ("Mathlib.Order.SupIndep", "theorem")]),
("Finset.map.eq_1", #[("Mathlib.Data.Finset.Fold", "theorem"), ("Mathlib.Data.Fintype.Basic", "theorem")]),
("Finsupp.equivFunOnFinite.congr_simp", #[("Mathlib.LinearAlgebra.Finsupp.LinearCombination", "theorem"), ("Mathlib.Data.Finsupp.Multiset", "theorem"), ("Mathlib.LinearAlgebra.Finsupp.Pi", "theorem"), ("Mathlib.Data.Finsupp.Fin", "theorem")]),
("Finsupp.linearEquivFunOnFinite.congr_simp", #[("Mathlib.LinearAlgebra.Basis.Defs", "theorem"), ("Mathlib.LinearAlgebra.LinearIndependent.Defs", "theorem")]),
("Function.Bijective.eq_1", #[("Mathlib.Data.Set.Operations", "theorem"), ("Mathlib.Data.List.Basic", "theorem")]),
("Function.Embedding.subtype.eq_1", #[("Mathlib.Topology.Algebra.InfiniteSum.Defs", "theorem"), ("Mathlib.LinearAlgebra.LinearIndependent.Defs", "theorem"), ("Mathlib.Combinatorics.Matroid.Map", "theorem")]),
("Function.Injective.eq_1", #[("Mathlib.Logic.Function.Basic", "theorem"), ("Mathlib.Data.Nat.Basic", "theorem")]),
("Function.IsFixedPt.eq_1", #[("Mathlib.Order.OmegaCompletePartialOrder", "theorem"), ("Mathlib.Dynamics.PeriodicPts.Defs", "theorem")]),
("Function.Surjective.eq_1", #[("Mathlib.Data.Sigma.Basic", "theorem"), ("Mathlib.Algebra.GroupWithZero.WithZero", "theorem")]),
("Function.comp_def._simp_3", #[("Mathlib.Analysis.Analytic.Composition", "theorem"), ("Mathlib.Analysis.Calculus.FDeriv.Comp", "theorem")]),
("Function.invFunOn.congr_simp", #[("Mathlib.Topology.Order.Basic", "theorem"), ("Mathlib.Combinatorics.Matroid.Map", "theorem")]),
("Function.onFun.eq_1", #[("Mathlib.Algebra.BigOperators.Group.Finset.Basic", "theorem"), ("Mathlib.Data.Finset.Sigma", "theorem"), ("Mathlib.Data.List.Permutation", "theorem")]),
("GetElem.getElem.hcongr_8", #[("Std.Tactic.BVDecide.LRAT.Internal.Clause", "theorem"), ("Batteries.Data.List.Lemmas", "theorem"), ("Mathlib.Data.List.InsertIdx", "theorem")]),
("HasDerivAt.congr_simp", #[("Mathlib.Analysis.Calculus.Deriv.Comp", "theorem"), ("Mathlib.Analysis.Calculus.Deriv.Pow", "theorem")]),
("HasDerivWithinAt.congr_simp", #[("Mathlib.Analysis.Calculus.Deriv.Comp", "theorem"), ("Mathlib.Analysis.Calculus.Deriv.Pow", "theorem")]),
("HasStrictDerivAt.congr_simp", #[("Mathlib.Analysis.Calculus.FDeriv.Analytic", "theorem"), ("Mathlib.Analysis.Calculus.Deriv.Comp", "theorem")]),
("Id.run.eq_1", #[("Init.Data.List.Scan.Lemmas", "theorem"), ("Std.Do.WP.SimpLemmas", "theorem")]),
("Ideal.Quotient.factor.eq_1", #[("Mathlib.RingTheory.Ideal.Quotient.Operations", "theorem"), ("Mathlib.RingTheory.Ideal.Quotient.PowTransition", "theorem")]),
("Ideal.Quotient.liftₐ.congr_simp", #[("Mathlib.RingTheory.Localization.AtPrime.Basic", "theorem"), ("Mathlib.RingTheory.TensorProduct.Quotient", "theorem")]),
("Ideal.quotientEquivAlgOfEq.congr_simp", #[("Mathlib.RingTheory.Artinian.Module", "theorem"), ("Mathlib.RingTheory.AdicCompletion.Algebra", "theorem")]),
("Int.gcd.eq_1", #[("Init.Data.Int.Linear", "theorem"), ("Init.Data.Rat.Lemmas", "theorem")]),
("Int.natMod.eq_1", #[("Mathlib.Algebra.Group.Submonoid.Membership", "theorem"), ("Mathlib.Logic.Equiv.Fin.Basic", "theorem")]),
("InvImage.eq_1", #[("Init.Data.String.Pattern.Basic", "theorem"), ("Init.Data.Range.Polymorphic.RangeIterator", "theorem"), ("Init.Data.String.Iterate", "theorem"), ("Init.Data.Iterators.Consumers.Access", "theorem"), ("Init.Data.Slice.Array.Iterator", "theorem"), ("Init.Data.Iterators.Combinators.Monadic.Take", "theorem"), ("Init.Data.Iterators.Combinators.Monadic.Attach", "theorem"), ("Std.Data.Iterators.Combinators.Monadic.StepSize", "theorem")]),
("IsNilpotent.eq_1", #[("Mathlib.RingTheory.Ideal.Operations", "theorem"), ("Mathlib.RingTheory.Nilpotent.Basic", "theorem")]),
("IsRelPrime.eq_1", #[("Mathlib.Data.Nat.GCD.Basic", "theorem"), ("Mathlib.Algebra.GroupWithZero.Associated", "theorem")]),
("IsScalarTower.toAlgHom.congr_simp", #[("Mathlib.Algebra.Algebra.Subalgebra.Tower", "theorem"), ("Mathlib.Algebra.MvPolynomial.Equiv", "theorem"), ("Mathlib.Algebra.Module.LocalizedModule.IsLocalization", "theorem"), ("Mathlib.RingTheory.Derivation.Basic", "theorem")]),
("IsUnit.liftRight.congr_simp", #[("Mathlib.RingTheory.Localization.AtPrime.Basic", "theorem"), ("Mathlib.RingTheory.Valuation.ExtendToLocalization", "theorem")]),
("LE.le.eq_1", #[("Aeneas.Std.Scalar.Core", "theorem"), ("Mathlib.Algebra.Module.Submodule.Lattice", "theorem")]),
("LatticeHom.mk.congr_simp", #[("Mathlib.Order.Sublattice", "theorem"), ("Mathlib.Order.Category.Lat", "theorem")]),
("Lean.Grind.ToInt.toInt.hcongr_4", #[("Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult", "theorem"), ("Mathlib.Data.Fin.SuccPred", "theorem"), ("Mathlib.Data.List.Permutation", "theorem")]),
("Lean.Grind.instToIntFinCoOfNatIntCast.hcongr_1", #[("Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult", "theorem"), ("Mathlib.Data.Fin.SuccPred", "theorem"), ("Mathlib.Data.List.Permutation", "theorem")]),
("LinearEquiv.ofEq.congr_simp", #[("Mathlib.LinearAlgebra.Basis.Basic", "theorem"), ("Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic", "theorem"), ("Mathlib.Analysis.Normed.Module.Span", "theorem")]),
("LinearEquiv.restrictScalars.congr_simp", #[("Mathlib.Algebra.Algebra.Equiv", "theorem"), ("Mathlib.LinearAlgebra.Basis.Defs", "theorem")]),
("LinearMap.compl₂.congr_simp", #[("Mathlib.RingTheory.TensorProduct.Maps", "theorem"), ("Mathlib.LinearAlgebra.SesquilinearForm.Basic", "theorem")]),
("LinearMap.linearProjOfIsCompl.congr_simp", #[("Mathlib.LinearAlgebra.Finsupp.VectorSpace", "theorem"), ("Mathlib.RingTheory.SimpleModule.Basic", "theorem")]),
("LinearMap.mk.congr_simp", #[("Mathlib.Algebra.Module.Equiv.Basic", "theorem"), ("Mathlib.Algebra.Module.Submodule.Equiv", "theorem"), ("Mathlib.LinearAlgebra.Finsupp.Defs", "theorem")]),
("LinearMap.restrictScalars.congr_simp", #[("Mathlib.LinearAlgebra.BilinearMap", "theorem"), ("Mathlib.LinearAlgebra.Finsupp.LinearCombination", "theorem"), ("Mathlib.Algebra.Module.LocalizedModule.Basic", "theorem")]),
("LinearMap.toMatrixAlgEquiv'.eq_1", #[("Mathlib.LinearAlgebra.Determinant", "theorem"), ("Mathlib.LinearAlgebra.Trace", "theorem")]),
("List.alternatingSum.eq_1", #[("Mathlib.Algebra.BigOperators.Fin", "theorem"), ("Mathlib.Data.Nat.Digits.Lemmas", "theorem")]),
("List.alternatingSum.eq_2", #[("Mathlib.Algebra.BigOperators.Fin", "theorem"), ("Mathlib.Data.Nat.Digits.Lemmas", "theorem")]),
("List.alternatingSum.eq_3", #[("Mathlib.Algebra.BigOperators.Fin", "theorem"), ("Mathlib.Data.Nat.Digits.Lemmas", "theorem")]),
("List.alternatingSum.eq_def", #[("Mathlib.Algebra.BigOperators.Fin", "theorem"), ("Mathlib.Data.Nat.Digits.Lemmas", "theorem")]),
("List.drop.eq_1", #[("Init.Data.Array.GetLit", "theorem"), ("Init.Data.List.TakeDrop", "theorem")]),
("List.drop.eq_2", #[("Init.Data.Array.GetLit", "theorem"), ("Init.Data.List.TakeDrop", "theorem")]),
("List.drop.eq_3", #[("Init.Data.Array.GetLit", "theorem"), ("Init.Data.List.TakeDrop", "theorem")]),
("List.drop.eq_def", #[("Init.Data.Array.GetLit", "theorem"), ("Init.Data.List.TakeDrop", "theorem")]),
("List.eraseIdx.eq_1", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.Erase", "theorem"), ("Init.Data.List.Nat.Basic", "theorem")]),
("List.eraseIdx.eq_2", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.Erase", "theorem"), ("Init.Data.List.Nat.Basic", "theorem")]),
("List.eraseIdx.eq_3", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.Erase", "theorem"), ("Init.Data.List.Nat.Basic", "theorem")]),
("List.eraseIdx.eq_def", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.Erase", "theorem"), ("Init.Data.List.Nat.Basic", "theorem")]),
("List.filter.match_1.congr_eq_1", #[("Batteries.Data.List.Lemmas", "theorem"), ("Mathlib.Data.List.Find", "theorem")]),
("List.filter.match_1.congr_eq_2", #[("Batteries.Data.List.Lemmas", "theorem"), ("Mathlib.Data.List.Find", "theorem")]),
("List.find?.eq_1", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.ToArray", "theorem")]),
("List.find?.eq_2", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.ToArray", "theorem")]),
("List.find?.eq_def", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.ToArray", "theorem")]),
("List.flatMapM.eq_1", #[("Init.Data.List.Monadic", "theorem"), ("Init.Data.List.ControlImpl", "theorem")]),
("List.flatMapM.loop.eq_def", #[("Init.Data.List.Monadic", "theorem"), ("Init.Data.List.ControlImpl", "theorem")]),
("List.foldl.eq_def", #[("Init.Data.List.MinMaxOn", "theorem"), ("Init.Data.List.Perm", "theorem")]),
("List.getLast.hcongr_3", #[("Mathlib.Data.List.Basic", "theorem"), ("Mathlib.Data.List.Induction", "theorem"), ("Mathlib.Data.List.Flatten", "theorem"), ("Mathlib.Data.List.Pairwise", "theorem")]),
("List.head.hcongr_3", #[("Mathlib.Data.List.Basic", "theorem"), ("Mathlib.Data.List.Flatten", "theorem"), ("Mathlib.Data.List.Pairwise", "theorem")]),
("List.insertIdx.eq_1", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.Nat.InsertIdx", "theorem"), ("Init.Data.List.Perm", "theorem")]),
("List.max.congr_simp", #[("Init.Data.List.MinMax", "theorem"), ("Init.Data.Array.Nat", "theorem"), ("Init.Data.Array.Int", "theorem")]),
("List.min.congr_simp", #[("Init.Data.List.MinMax", "theorem"), ("Init.Data.Array.Nat", "theorem"), ("Init.Data.Array.Int", "theorem")]),
("List.modify.eq_1", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.Nat.Modify", "theorem")]),
("List.revzip.eq_1", #[("Mathlib.Data.List.Sublists", "theorem"), ("Mathlib.Data.List.Zip", "theorem")]),
("List.take.eq_1", #[("Init.Data.List.TakeDrop", "theorem"), ("Init.Data.List.Impl", "theorem")]),
("List.take.eq_2", #[("Init.Data.List.TakeDrop", "theorem"), ("Init.Data.List.Impl", "theorem")]),
("List.take.eq_3", #[("Init.Data.List.TakeDrop", "theorem"), ("Init.Data.List.Impl", "theorem")]),
("List.take.eq_def", #[("Init.Data.List.TakeDrop", "theorem"), ("Init.Data.List.Impl", "theorem")]),
("List.takeWhile.eq_1", #[("Init.Data.List.TakeDrop", "theorem"), ("Init.Data.List.Impl", "theorem")]),
("List.takeWhile.eq_2", #[("Init.Data.List.TakeDrop", "theorem"), ("Init.Data.List.Impl", "theorem")]),
("List.takeWhile.eq_def", #[("Init.Data.List.TakeDrop", "theorem"), ("Init.Data.List.Impl", "theorem")]),
("List.zipIdx.eq_1", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.Sort.Lemmas", "theorem")]),
("List.zipIdx.eq_2", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.Sort.Lemmas", "theorem")]),
("List.zipIdx.eq_def", #[("Init.Data.List.Impl", "theorem"), ("Init.Data.List.Sort.Lemmas", "theorem")]),
("LowerSet.mk.congr_simp", #[("Mathlib.Topology.Spectral.Prespectral", "theorem"), ("Mathlib.Combinatorics.Matroid.Basic", "theorem")]),
("M31AcceptFiber.P31.eq_1", #[("M31EightLimbSuccessCount", "theorem"), ("M31RetryMassRational", "theorem")]),
("Mathlib.Tactic.TermCongr.cHole.congr_simp", #[("Mathlib.Algebra.GCDMonoid.Multiset", "theorem"), ("Mathlib.LinearAlgebra.Complex.Module", "theorem")]),
("Matrix.toLinAlgEquiv'.eq_1", #[("Mathlib.LinearAlgebra.Determinant", "theorem"), ("Mathlib.LinearAlgebra.Trace", "theorem")]),
("MonadExcept.orElse.eq_1", #[("Std.Do.WP.SimpLemmas", "theorem"), ("Std.Internal.Do.WP.Lemmas", "theorem")]),
("MonoidHom.mk.congr_simp", #[("Mathlib.Algebra.Group.Units.Equiv", "theorem"), ("Mathlib.Algebra.Group.Equiv.TypeTags", "theorem"), ("Mathlib.Algebra.FreeMonoid.Basic", "theorem"), ("Mathlib.Algebra.Algebra.Defs", "theorem"), ("Mathlib.Algebra.Group.Graph", "theorem"), ("Mathlib.Topology.Algebra.Constructions", "theorem"), ("Mathlib.GroupTheory.MonoidLocalization.Basic", "theorem")]),
("MonoidWithZeroHom.mk.congr_simp", #[("Mathlib.Analysis.Real.Sqrt", "theorem"), ("Mathlib.Data.Complex.Basic", "theorem"), ("Mathlib.Data.Int.WithZero", "theorem"), ("Mathlib.RingTheory.Valuation.ValuativeRel.Basic", "theorem"), ("Mathlib.Topology.Algebra.Valued.ValuedField", "theorem")])]
  let some path ← IO.getEnv "LEAN_PATH" | throw (IO.userError "LEAN_PATH missing")
  let roots := path.splitOn ":"
  let out ← IO.FS.Handle.mk "evidence/raw-batch-003.jsonl" .write
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
