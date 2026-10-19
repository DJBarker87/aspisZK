import CompPolyFiniteRootSampler
import CompPolyGeneralRootsProgram
import RRVectorNormalizedCompleteV3
import RRScannedNormalizedTransition
import RRRootDescent
import RRVectorActualScannerV2
import RRFiniteCoeffScannerV9

open Polynomial CompPoly
noncomputable section
namespace AspisR1.RRFiniteRootSamplerNormalizedStateBridge

def normalizedRuntimeState (gs : List (List K)) (a : K) (M ell v : Nat) :
    List (List K) :=
  (RRVectorNormalizedRows.rowsThrough gs a M (M + ell)).drop v

/-- Build the sampler input from the executable dense coefficient row. -/
def normalizedRuntimeRootPolynomial {K : Type*} [Field K] [BEq K]
    [LawfulBEq K] (gs : List (List K)) (a : K) (M v : Nat) : CPolynomial K :=
  CPolynomial.ofArray (RRVectorRowPolynomialBridge.row gs a M v).toArray

theorem ofArray_toPolynomial {K : Type*} [Field K] [BEq K] [LawfulBEq K]
    (cs : List K) :
    (CPolynomial.ofArray cs.toArray).toPoly = RRDenseCoeffVector.toPolynomial cs := by
  apply Polynomial.ext
  intro n
  rw [CPolynomial.ofArray_toPoly, CPolynomial.Raw.coeff_toPoly]
  rw [RRDenseCoeffVector.coeff_toPolynomial]
  simp [RRDenseCoeffVector.coeffAt]

variable {K : Type*} [Field K] [BEq K] [LawfulBEq K]
  [DecidableEq K] [Fintype K]

def runFromFiniteTapeGeneral (p : CPolynomial K) (q t : Nat)
    (H : {i : Nat // i ∈ Finset.range (p.natDegree-1)} → Fin t → K × K) :
    Option (List K) × Nat :=
  (eval (extend (Finset.range (p.natDegree-1)) H (fun _ => (0,0)))
    (AspisR1.CompPolyGeneralRootsProgram.generalRootsProgram p q t)).2

/-- The executed first-nonzero scanner selects row `v`; that exact runtime
coefficient row, packaged as an array-backed CPolynomial, is the child at
`X=0`. A successful finite-tape root run contains the constant term of every
actual normalized-child root, and the scanner's root-preservation equation
lifts that root back to the prior affine parent. -/
theorem scanned_finite_sampler_covers_normalized_child_constants
    (gs : List (List K)) (a : K) (M L ell v : Nat) (p0 : K[X])
    (hp0 : p0 ≠ 0) (hinput : RRVectorRowPolynomialBridge.inputPolynomial gs 0 = p0)
    (hL : p0.rootMultiplicity a ≤ L)
    (hscan : RRFiniteCoeffScannerV9.firstNonzeroFullRows
      (RRVectorActualScanner.rowsUpTo gs a M L) =
        some (v, RRVectorRowPolynomialBridge.row gs a M v))
    (hLspan : L ≤ M + ell)
    (hdegree : ∀ i ≤ M, (RRVectorRowPolynomialBridge.inputPolynomial gs i).natDegree ≤ ell)
    (q t : Nat) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range
      ((normalizedRuntimeRootPolynomial gs a M v).natDegree - 1)} → Fin t → K × K)
    (roots : List K)
    (hsuccess : (runFromFiniteTapeGeneral
      (normalizedRuntimeRootPolynomial gs a M v) q t H).1 = some roots)
    (f : K[X])
    (hroot : (RRVectorNormalizedRows.actualChild gs a M v).eval f = 0) :
    (f.eval 0 ∈ roots) ∧
      (RRVectorNormalizedRows.actualParent gs M).eval (C a + X * f) = 0 ∧
      (normalizedRuntimeState gs a M ell v)[0]? =
        some (RRVectorRowPolynomialBridge.row gs a M v) ∧
      (RRVectorNormalizedComplete.boundedState gs a M ell v)[0]? =
        some (RRVectorNormalizedComplete.normalizedModelRow gs a M v 0) ∧
      (normalizedRuntimeRootPolynomial gs a M v).toPoly ≠ 0 := by
  let Q := (RRVectorNormalizedRows.actualParent gs M).comp (RRRootDescent.affine a)
  let child := RRVectorNormalizedRows.actualChild gs a M v
  let row := RRVectorRowPolynomialBridge.row gs a M v
  let samplerPoly := normalizedRuntimeRootPolynomial gs a M v
  obtain ⟨v0, hv0, hscan0, _, hlower0⟩ :=
    RRVectorActualScanner.actual_row_scanner_finds_first_slice
      gs a M L p0 hp0 hinput hL
  have hroweq : v0 = v := by
    have heq := hscan0.symm.trans hscan
    have hpair := Option.some.inj heq
    exact congrArg Prod.fst hpair
  subst v0
  have htransition := RRRootDescent.scanned_normalized_transition
    gs p0 M L a hp0 hinput hL
  obtain ⟨w, hw, hscanTransition, hspecNonzero, hspecDegree, hrootPres⟩ := htransition
  have hweq : w = v := by
    have heq := hscanTransition.symm.trans hscan
    have hpair := Option.some.inj heq
    exact congrArg Prod.fst hpair
  subst w
  have hv : v ≤ M + ell := by omega
  have hcomp := RRRootDescent.parentFromSlices_comp
    (RRVectorRowPolynomialBridge.inputPolynomial gs) M a
  have hlowerslice : ∀ k < v,
      RRActualBivariateTaylorBridge.xCoeffSlice Q k = 0 := by
    intro k hk
    simpa [RRActualBivariateTaylorBridge.fixedParentCoeffSlice,
      RRVectorNormalizedRows.actualParent, Q, hcomp] using hlower0 k hk
  have hlower : ∀ j k, k < v →
      ((((RRVectorNormalizedRows.actualParent gs M).comp
        (RRRootDescent.affine a)).coeff j).coeff k = 0) := by
    intro j k hk
    have hz := congrArg (fun r : K[X] => r.coeff j) (hlowerslice k hk)
    simpa only [RRActualBivariateTaylorBridge.xCoeffSlice_coeff] using hz
  have hrowpoly : RRDenseCoeffVector.toPolynomial row =
      RRActualBivariateTaylorBridge.fixedParentCoeffSlice
        (RRVectorRowPolynomialBridge.inputPolynomial gs) a M v := by
    simpa [row, RRActualBivariateTaylorBridge.fixedParentCoeffSlice] using
      RRVectorRowPolynomialBridge.rowPolynomial_eq_parentSlice gs a M v
  have hpoly : samplerPoly.toPoly =
      RRActualBivariateTaylorBridge.fixedParentCoeffSlice
        (RRVectorRowPolynomialBridge.inputPolynomial gs) a M v := by
    calc
      samplerPoly.toPoly = RRDenseCoeffVector.toPolynomial row := by
        simpa [samplerPoly, normalizedRuntimeRootPolynomial, row] using
          ofArray_toPolynomial row
      _ = RRActualBivariateTaylorBridge.fixedParentCoeffSlice
          (RRVectorRowPolynomialBridge.inputPolynomial gs) a M v := hrowpoly
  have hspec := RRRootDescent.normalized_specialization_eq_slice Q v hlowerslice
  have hpolySpec : samplerPoly.toPoly =
      child.map (Polynomial.evalRingHom (0 : K)) := by
    rw [hpoly, RRActualBivariateTaylorBridge.fixedParentCoeffSlice,
      ← hcomp]
    simpa [child, RRVectorNormalizedRows.actualChild,
      RRVectorNormalizedRows.actualParent, Q] using hspec.symm
  have hpnonzero : samplerPoly.toPoly ≠ 0 := by
    rw [hpolySpec]
    simpa [child, RRVectorNormalizedRows.actualChild,
      RRVectorNormalizedRows.actualParent, Q] using hspecNonzero
  have hcorrect := AspisR1.CompPolyGeneralRootsProgram.generalRoots_correct
    samplerPoly q t hq hpnonzero
  have hrun := all_eval
    (extend (Finset.range (samplerPoly.natDegree-1)) H (fun _ => (0,0)))
    _ _ hcorrect
  have hresult :
      AspisR1.CompPolySequentialRootsContract.RootResult samplerPoly
        (runFromFiniteTapeGeneral samplerPoly q t H) := by
    simpa [runFromFiniteTapeGeneral] using hrun
  rcases hresult with ⟨_, hroots⟩
  have hmembership := (hroots roots hsuccess).1
  have hconstant := RRRootDescent.constant_coefficient_is_root child f hroot
  have hrootSampler : Polynomial.IsRoot samplerPoly.toPoly (f.eval 0) := by
    change samplerPoly.toPoly.eval (f.eval 0) = 0
    rw [hpolySpec]
    exact hconstant
  have hstate : (normalizedRuntimeState gs a M ell v)[0]? = some row := by
    have hbase :
        (RRVectorNormalizedRows.rowsThrough gs a M (M + ell))[v]? = some row := by
      simp [RRVectorNormalizedRows.rowsThrough, row, List.getElem?_ofFn]
    rw [normalizedRuntimeState, List.getElem?_drop]
    simpa using hbase
  have hmodelstate := RRVectorNormalizedComplete.all_index_readback
    gs a M ell v hdegree hlower hv 0
  have hmodelstate0 :
      (RRVectorNormalizedComplete.boundedState gs a M ell v)[0]? =
        some (RRVectorNormalizedComplete.normalizedModelRow gs a M v 0) := by
    have hlen : 0 < M + ell + 1 - v := by omega
    simpa [hlen] using hmodelstate.1
  have hparent :
      (RRVectorNormalizedRows.actualParent gs M).eval (C a + X * f) = 0 := by
    apply hrootPres f
    exact hroot
  exact ⟨hmembership.mp hrootSampler, hparent, hstate,
    hmodelstate0, hpnonzero⟩

#print axioms ofArray_toPolynomial
#print axioms scanned_finite_sampler_covers_normalized_child_constants
end AspisR1.RRFiniteRootSamplerNormalizedStateBridge
