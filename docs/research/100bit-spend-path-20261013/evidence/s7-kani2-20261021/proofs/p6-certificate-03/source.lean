import S7Kani2AccumulatorTotal
import S7Kani2BasisLoop
import S7Kani2OwnedRow
import S7Kani2OwnedRowRefinement
import S7Kani2OwnedPushModel
import S7Kani2PrefixLoop
import S7Kani2RowSweep
import S7Kani2BackendArithmetic
import S7Kani2ConstructorInvariant
import S7Kani2VectorPrefix
import S7Kani2QueryComposition
import S7Kani2SpecificationBound

/-! A named LOCAL P6 proof packet. Its type records exactly what is proved.
It is not an inhabitant of the headline's arbitrary S7/R17 propositions or a
complete production query/caller refinement. Rust source bindings and Kani
results are external evidence, never Lean axioms. -/
set_option autoImplicit false
namespace AspisR1.S7Kani2P6Certificate
open Aeneas Aeneas.Std Result

structure LocalCertificate : Prop where
  rowDriver : ∀ (backend : S7Kani2AccumulatorLoop.Backend)
    (basis : Array U32 256#usize) (power : S7Kani2AccumulatorLoop.K)
    (next width j : Usize) (n : Nat) (state : S7Kani2AccumulatorLoop.State),
    width.val≤256 → j.val+n=width.val →
    S7Kani2AccumulatorLoop.accumulate_rows_owned backend state.1 state.2 basis power next width j =
      S7Kani2AccumulatorLoop.iterate (S7Kani2AccumulatorLoop.step backend basis power next width) n j state
  rowWords : ∀ (x : Fin 4 → U64) (power : S7Kani2OwnedRow.K)
    (basis : U32) (terms : Nat),
    (∀ j, (S7Kani2OwnedRowRefinement.powerLimb power j).val<2^31-1) →
    basis.val<2^31-1 →
    (∀ j, (x j).val<2^34+(terms%4)*(2^31-2)^2) →
    ∃ y : Fin 4 → U64,
      S7Kani2OwnedRow.residue_owned (S7Kani2OwnedRowRefinement.makeRow x) power basis
        (decide (terms%4=3)) = ok (S7Kani2OwnedRowRefinement.makeRow y) ∧
      ∀ j, (y j).val = AspisR1BatchedFoldSourceStep.sourcePush terms (x j).val
        ((S7Kani2OwnedRowRefinement.powerLimb power j).val*basis.val)
  vecPush : ∀ (weights : S7Kani2AccumulatorLoop.BatchedWeights) (index : Usize)
    (power : S7Kani2AccumulatorLoop.K) (basis : U32) (x : Fin 4 → U64),
    index.val<weights.raw.length →
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice S7Kani2OwnedRow.Row)
      weights.raw index=ok (S7Kani2OwnedRowRefinement.makeRow x) →
    (∀ j, (S7Kani2OwnedRowRefinement.powerLimb power j).val<2^31-1) →
    basis.val<2^31-1 →
    (∀ j, (x j).val<2^34+(weights.terms.val%4)*(2^31-2)^2) →
    ∃ y : Fin 4 → U64,
      S7Kani2OwnedPush.push_owned weights index power basis =
        ok {weights with raw := weights.raw.set index (S7Kani2OwnedRowRefinement.makeRow y)} ∧
      ∀ j, (y j).val = AspisR1BatchedFoldSourceStep.sourcePush weights.terms.val (x j).val
        ((S7Kani2OwnedRowRefinement.powerLimb power j).val*basis.val)
  prefixLoop : ∀ (flat prefixes : alloc.vec.Vec U32) (product : U32) (index : Usize) (fuel : Nat),
    flat.val.length≤110 → index.val+fuel=flat.val.length → prefixes.val.length+fuel≤110 →
    ∃ prefixesOut productOut,
      S7Kani2PrefixLoop.prefixes_owned flat prefixes product index=ok (flat,prefixesOut,productOut) ∧
      (prefixesOut.val,productOut)=S7Kani2PrefixLoop.model (flat.val.drop index.val) prefixes.val product
  basisDriver : ∀ (multiply : U32 → U32 → Result U32)
    (basis : S7Kani2BasisLoop.Basis) (node : U32) (n j : Usize) (fuel : Nat),
    n.val≤128 → j.val+fuel=n.val →
    S7Kani2BasisLoop.basis_block_owned multiply basis node n j =
      S7Kani2BasisLoop.iterate (S7Kani2BasisLoop.step multiply node n) fuel j basis
  rowSweep : ∀ (power : S7OwnedP6RowContract.Row) (basis : Nat → Nat)
    (terms start count : Nat) (rows : S7Kani2RowSweep.Rows),
    S7OwnedP6LoopSimulation.run (S7Kani2RowSweep.sourceStep power basis terms) count start rows =
      S7OwnedP6LoopSimulation.run (S7Kani2RowSweep.referenceStep power basis terms) count start rows
  constructor : ∀ (rows : List (S7Kani2ConstructorInvariant.Row U32)), rows.length≤22 →
    (S7Kani2ConstructorInvariant.gather rows ⟨[],[]⟩).flat.length=5*rows.length ∧
    (S7Kani2ConstructorInvariant.gather rows ⟨[],[]⟩).lineZ.length=rows.length ∧
    (S7Kani2ConstructorInvariant.gather rows ⟨[],[]⟩).flat.length≤110 ∧
    (S7Kani2ConstructorInvariant.gather rows ⟨[],[]⟩).lineZ.length≤22
  backendMultiply : ∀ xy : S7Kani2BackendArithmetic.CanonicalPair,
    ∃ z, S7Kani2BackendArithmetic.multiply xy=ok z ∧
      S7Kani2BackendArithmetic.Canonical z ∧
      ExtractedCurrentQM31Exact.decode z =
        ExtractedCurrentQM31Exact.decode xy.val.1 * ExtractedCurrentQM31Exact.decode xy.val.2
  queryDriver : ∀ (S E : Type) (cursor : S → Usize)
    (query : S → Result (Except E S)) (finish : Usize) (state : S) (n : Nat),
    (cursor state).val+n=finish.val →
    (∀ s t, (cursor s).val<finish.val → query s=ok (.ok t) →
      (cursor t).val=(cursor s).val+1) →
    S7Kani2QueryComposition.run cursor query finish state =
      S7Kani2QueryComposition.iterate query n state

theorem p6_local_certificate : LocalCertificate where
  rowDriver := S7Kani2AccumulatorLoop.extracted_loop_composition
  rowWords := S7Kani2OwnedRowRefinement.literal_row_refines_model
  vecPush := S7Kani2OwnedPushModel.push_refines_model
  prefixLoop := S7Kani2PrefixLoop.prefixes_refines
  basisDriver := S7Kani2BasisLoop.extracted_basis_block_composition
  rowSweep := S7Kani2RowSweep.source_sweep_refines
  constructor := S7Kani2ConstructorInvariant.constructor_bounds
  backendMultiply := S7Kani2BackendArithmetic.multiply_exact
  queryDriver := fun _ _ => S7Kani2QueryComposition.query_loop_composition

#print axioms p6_local_certificate
end AspisR1.S7Kani2P6Certificate
