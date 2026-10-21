import S7Kani2P6Certificate
import S7Kani3GeometryStorage
import S7Kani3BasisTotal
import S7Kani3WideBackend
import S7Kani3CallerTrace
import S7Kani3Checkpoint

/-! Named partial P6 route at actual owned operations and the S8 mutable
finish. Full frozen query/TX membership, geometry/backend joins and the
release interpretation remain obligations; this is not global S7 evidence. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S7Kani3P6RouteCertificate
open Aeneas Aeneas.Std Result
open S7Kani2BackendArithmetic (Wide CanonicalWide)
open ExtractedCurrentQM31Exact (decode)

structure P6RouteCertificate : Prop where
  previous : S7Kani2P6Certificate.LocalCertificate
  s8 : S8Kani2CallerJoin.P6Certificate
  productionBasisTotal : ∀ (basis : S7Kani2BasisLoop.Basis) (node : U32),
    ∃ out, S7Kani3BasisOuter.basis_levels_owned basis node 64#usize 1#usize=ok out
  inverseTotal : ∀ (flat prefixes inverse : alloc.vec.Vec U32) (suffix : U32) (index : Usize),
    index.val ≤ 110 → index.val ≤ flat.val.length → index.val ≤ prefixes.val.length →
    index.val ≤ inverse.val.length →
    ∃ out, S7Kani3InverseLoop.inverse_owned flat prefixes inverse suffix index=ok out ∧
      out.val=S7Kani3InverseLoop.model flat.val prefixes.val index.val inverse.val suffix ∧
      out.val.length=inverse.val.length
  wideProduct : ∀ (x y : Wide), CanonicalWide x → CanonicalWide y →
    ∃ z, S7Kani3WideBackend.mulWide x y=ok z ∧ CanonicalWide z ∧
      decode z.c0=decode x.c0*decode y.c0+S7Kani3WideBackend.u*(decode x.c1*decode y.c1) ∧
      decode z.c1=decode x.c0*decode y.c1+decode x.c1*decode y.c0
  phase : ∀ (products : List Nat) (terms raw : Nat),
    S7Kani3PhaseInvariant.Phase terms raw →
    (∀ p∈products,p ≤ AspisR1BatchedFoldSourceStep.productCap) →
    S7Kani3PhaseInvariant.Phase (terms+products.length)
      (S7Kani3PhaseInvariant.run terms raw products)
  caller : ∀ (old : S8OwnedP6Finish.Weights) (state : S7Kani2AccumulatorLoop.BatchedWeights)
    (sum : S7Kani3CallerTrace.Sum), S7Kani3CallerTrace.PushTrace old state sum →
    S8Kani2CallerJoin.CallerInvariant state.raw old sum
  checkpoint : ∀ (first second : List Nat) (terms raw : Nat),
    S7Kani3PhaseInvariant.run 0
      (S7Kani3PhaseInvariant.run terms raw first%AspisR1BatchedFoldSourceStep.modulus)
      second%AspisR1BatchedFoldSourceStep.modulus =
      S7Kani3PhaseInvariant.run terms raw (first++second)%AspisR1BatchedFoldSourceStep.modulus

theorem p6_route_certificate : P6RouteCertificate where
  previous := S7Kani2P6Certificate.p6_local_certificate
  s8 := S8Kani2CallerJoin.p6_certificate
  productionBasisTotal := S7Kani3BasisTotal.production_basis_total
  inverseTotal := S7Kani3InverseLoop.inverse_refines
  wideProduct := S7Kani3WideBackend.mul_wide_exact
  phase := S7Kani3PhaseInvariant.run_phase
  caller := S7Kani3CallerTrace.reached_invariant
  checkpoint := S7Kani3Checkpoint.transaction_splice

#print axioms p6_route_certificate
end AspisR1.S7Kani3P6RouteCertificate
