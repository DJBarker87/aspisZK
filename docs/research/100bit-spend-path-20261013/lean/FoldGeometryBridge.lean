import FoldRuntimeAlgebra
import FoldStoredGeometry

/-! Consumers of the symbolic fold/domain facts. Source execution is not
assumed implicitly: the definitions below are field interpretations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FoldGeometryBridge
open AspisCircleGroupOrder AspisCircleTensorBinding
open AspisV5ComponentCConcreteFoldLinearity AspisV7ExactOneFoldDomains
open AspisV5FriReleasedLineGeometry
open AspisR1.FoldStoredGeometry AspisR1.FoldRuntimeAlgebra
variable {K : Type*} [Field K] [Algebra (ZMod P) K]

/-- The two source line coordinates, embedded into the accumulator field. -/
def lx (u : Fin 65536) : K :=
  algebraMap (ZMod P) K (sourceX18 (AspisR1.childIndex u 0))
def ly (u : Fin 65536) : K :=
  algebraMap (ZMod P) K (sourceX18 (AspisR1.childIndex u 3))
def lz (u : Fin 65536) : K := 2 * lx u ^ 2 - 1

/-- The exact source denominator z is the model's intermediate log-17 x. -/
theorem z_eq_model (u : Fin 65536) :
    lz (K := K) u = algebraMap (ZMod P) K
      (storedLine17X (binaryChildIndex u)) := by
  have h := congrArg (algebraMap (ZMod P) K) (AspisR1.storedLine18_t2_slot0 u)
  simpa only [lz, lx, x18_eq_stored, child_eq_model, doubledFactor,
    map_sub, map_mul, map_pow, map_ofNat, map_one] using h

/-- On the nonzero branch tested by QueryGeometry, the line expression
is the model fold at the actual stored-domain inverse tuple. -/
theorem line_at_stored (alpha : K) (u : Fin 65536) (values : Fin 4 → K)
    (h2 : (2 : K) ≠ 0) (hx : lx (K := K) u ≠ 0)
    (hy : ly (K := K) u ≠ 0) (hz : lz (K := K) u ≠ 0) :
    line alpha (lx u) (ly u) (lz u) values =
      lineFoldValue alpha
        (2 * algebraMap (ZMod P) K
          (storedFirstLineX18 (AspisR1.childIndex u 0)))⁻¹
        (2 * algebraMap (ZMod P) K
          (storedFirstLineX18 (AspisR1.childIndex u 2)))⁻¹
        (2 * algebraMap (ZMod P) K
          (storedLine17X (binaryChildIndex u)))⁻¹ values := by
  rw [line_eq_model alpha (lx u) (ly u) (lz u) values h2 hx hy hz]
  have hcoord : -ly (K := K) u = algebraMap (ZMod P) K
      (storedFirstLineX18 (AspisR1.childIndex u 2)) := by
    unfold ly
    rw [runtime_y, map_neg, neg_neg, x18_eq_stored]
  rw [hcoord, z_eq_model]
  simp only [lx, x18_eq_stored]

/-- The source natural-basis table commutes with the four-to-one point map. -/
theorem natural_poly_child (u : Fin 65536) (s : Fin 4) (q : Nat) :
    (naturalLinePoly (ZMod P) (4 * q)).eval
        (sourceX18 (AspisR1.childIndex u s)) =
      (naturalLinePoly (ZMod P) q).eval (storedLine16X u) := by
  rw [← naturalLineValue_eq_eval, ← naturalLineValue_eq_eval,
    AspisV5FriNaturalBasisRadix4.naturalLineValue_four_mul, quartet_t4]

omit [Algebra (ZMod P) K] in
/-- Relation input arrays have no intrinsic stored-domain invariant.
In particular, an arbitrary x16/x18 table cannot be identified with the
model without its construction or a named equality hypothesis. -/
theorem unconstrained_table_counterexample (x : Fin 65536 → K) :
    (fun i => x i + 1) (0 : Fin 65536) ≠ x 0 := by
  simp

#print axioms natural_poly_child
#print axioms z_eq_model
#print axioms line_at_stored
#print axioms unconstrained_table_counterexample
end AspisR1.FoldGeometryBridge
