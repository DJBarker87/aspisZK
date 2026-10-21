import FoldGeometryBridge

/-! The production consumer performs one T2 after the constructor's stored z.
These are symbolic model joins, not a claim about an unproved Rust run. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S7OwnedP6StoredNode
open AspisCircleGroupOrder AspisCircleTensorBinding AspisV7ExactOneFoldDomains
open AspisV5FriReleasedLineGeometry AspisV5ComponentCConcreteFoldLinearity
open FoldStoredGeometry FoldGeometryBridge FoldRuntimeAlgebra
variable {K : Type*} [Field K] [Algebra (ZMod P) K]

theorem extra_t2_is_final_node (u : Fin 65536) :
    2 * (lz (K := K) u)^2 - 1 =
      algebraMap (ZMod P) K (storedLine16X u) := by
  have h := congrArg (algebraMap (ZMod P) K) (x16_eq_stored u)
  simpa only [sourceX16,doubledFactor,lz,lx,map_sub,map_mul,map_pow,
    map_ofNat,map_one] using h

theorem inverse_line_fold_to_model (alpha : K) (u : Fin 65536) (values : Fin 4 → K)
    (h2 : (2 : K) ≠ 0) (hx : lx (K := K) u ≠ 0)
    (hy : ly (K := K) u ≠ 0) (hz : lz (K := K) u ≠ 0) :
    lineWithInverses alpha (lx u)⁻¹ (ly u)⁻¹ (lz u)⁻¹ values =
      lineFoldValue alpha
        (2 * algebraMap (ZMod P) K
          (storedFirstLineX18 (AspisR1.childIndex u 0)))⁻¹
        (2 * algebraMap (ZMod P) K
          (storedFirstLineX18 (AspisR1.childIndex u 2)))⁻¹
        (2 * algebraMap (ZMod P) K
          (storedLine17X (binaryChildIndex u)))⁻¹ values := by
  rw [line_with_inverses_eq]
  exact line_at_stored alpha u values h2 hx hy hz

#print axioms extra_t2_is_final_node
#print axioms inverse_line_fold_to_model
end AspisR1.S7OwnedP6StoredNode
