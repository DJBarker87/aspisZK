import FoldGeometryBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.Stage2FinishGeometry
open AspisCircleGroupOrder AspisV7ExactOneFoldDomains
open AspisV5ComponentCConcreteFoldLinearity AspisV5FriReleasedLineGeometry
variable {F : Type*} [Field F] [Algebra (ZMod P) F]

/-- The optimized inverse-tuple expression consumed by a stage-2 query
commutes with the exact stored-domain LineFold model, including slot 3's sign.
S7/R13 must identify the returned tuple and authenticated values with these inputs. -/
theorem line_with_inverse_tuple (alpha : F) (u : Fin 65536) (values : Fin 4 → F)
    (h2 : (2 : F) ≠ 0) (hx : FoldGeometryBridge.lx (K := F) u ≠ 0)
    (hy : FoldGeometryBridge.ly (K := F) u ≠ 0) (hz : FoldGeometryBridge.lz (K := F) u ≠ 0) :
    FoldRuntimeAlgebra.lineWithInverses alpha
      (FoldGeometryBridge.lx u)⁻¹ (FoldGeometryBridge.ly u)⁻¹ (FoldGeometryBridge.lz u)⁻¹ values =
    lineFoldValue alpha
      (2 * algebraMap (ZMod P) F (storedFirstLineX18 (childIndex u 0)))⁻¹
      (2 * algebraMap (ZMod P) F (storedFirstLineX18 (childIndex u 2)))⁻¹
      (2 * algebraMap (ZMod P) F (storedLine17X (binaryChildIndex u)))⁻¹ values := by
  rw [FoldRuntimeAlgebra.line_with_inverses_eq]
  exact FoldGeometryBridge.line_at_stored alpha u values h2 hx hy hz

/-- Circle branch of the same commutation; S7 supplies the source fibre
coordinates and the successful zero guard supplies the nonzero premises. -/
theorem circle_with_inverse_tuple (alpha x y : F) (values : Fin 4 → F)
    (h2 : (2 : F) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    FoldRuntimeAlgebra.circleWithInverses alpha x⁻¹ y⁻¹ values =
    lineFoldValue alpha (2 * y)⁻¹ (2 * -y)⁻¹ (2 * x)⁻¹ values := by
  rw [FoldRuntimeAlgebra.circle_with_inverses_eq]
  exact FoldRuntimeAlgebra.circle_eq_model alpha x y values h2 hx hy

#print axioms line_with_inverse_tuple
#print axioms circle_with_inverse_tuple
end AspisR1.Stage2FinishGeometry
end
