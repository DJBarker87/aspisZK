import AspisFormal.V7ExactOneFoldDomains
import R1ZCircleFoldMathV1

import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

namespace R1ZQueryGeometryValuesV1

open AspisCircleGroupOrder AspisCircleTensorBinding
open AspisV5ComponentCConcreteFoldLinearity

/-- The source `fast_domain::line_node`: use the x-coordinate of the exact
stored fibre point and apply the deployed `2*x^2-1` step. -/
def sourceLineNode (u : Fin 262144) : ZMod P :=
  2 * (X (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20 u)) ^ 2 - 1

theorem sourceLineNode_eq_stored (u : Fin 262144) :
    sourceLineNode u = AspisV7ExactOneFoldDomains.storedFirstLineX18 u := by
  unfold sourceLineNode
  rw [AspisV7ExactOneFoldDomains.storedFirstLineX18_eq_doubled]
  simp [doubledFactor]

/-- Parent query index used by `u/4*4` and `u/4*4+3` in `QueryGeometry`. -/
def sourceParent (u : Fin 262144) : Fin 65536 :=
  ⟨u.val / 4, by have hu := u.isLt; omega⟩

theorem sourceParent_child0_val (u : Fin 262144) :
    (childIndex (sourceParent u) 0).val = (u.val / 4) * 4 := by
  unfold sourceParent
  simp only [childIndex, Fin.val_mk]
  omega

theorem sourceParent_child3_val (u : Fin 262144) :
    (childIndex (sourceParent u) 3).val = (u.val / 4) * 4 + 3 := by
  unfold sourceParent
  simp only [childIndex, Fin.val_mk]
  omega

/-- The five mathematical denominators assembled by `QueryGeometry` for a
parent `v`. Circle coordinates are supplied by `fibre_point`; the line
coordinates are the exact stored children. -/
def queryGeometryValues (px py : ZMod P) (v : Fin 65536) : Fin 5 → ZMod P :=
  ![px, py,
    sourceLineNode (childIndex v 0),
    sourceLineNode (childIndex v 3),
    2 * sourceLineNode (childIndex v 0) ^ 2 - 1]

@[simp] theorem queryGeometryValues_lineX (px py : ZMod P) (v : Fin 65536) :
    queryGeometryValues px py v 2 =
      AspisV7ExactOneFoldDomains.storedFirstLineX18 (childIndex v 0) := by
  simp [queryGeometryValues, sourceLineNode_eq_stored]

@[simp] theorem queryGeometryValues_lineY (px py : ZMod P) (v : Fin 65536) :
    queryGeometryValues px py v 3 =
      AspisV7ExactOneFoldDomains.storedFirstLineX18 (childIndex v 3) := by
  simp [queryGeometryValues, sourceLineNode_eq_stored]

@[simp] theorem queryGeometryValues_lineZ (px py : ZMod P) (v : Fin 65536) :
    queryGeometryValues px py v 4 =
      2 * AspisV7ExactOneFoldDomains.storedFirstLineX18 (childIndex v 0) ^ 2 - 1 := by
  simp [queryGeometryValues, sourceLineNode_eq_stored]

/-- Pointwise inverse vector corresponding to the five entries that the
source prefix-product/backward-pass routine is intended to emit. -/
def pointwiseInverses (px py : ZMod P) (v : Fin 65536) : Fin 5 → ZMod P :=
  fun i => (queryGeometryValues px py v i)⁻¹

def sourceLineInverse (v : Fin 65536) : Fin 3 → ZMod P :=
  ![(2 * AspisV7ExactOneFoldDomains.storedFirstLineX18 (childIndex v 0))⁻¹,
    -(2 * AspisV7ExactOneFoldDomains.storedFirstLineX18 (childIndex v 3))⁻¹,
    (2 * (2 * AspisV7ExactOneFoldDomains.storedFirstLineX18 (childIndex v 0) ^ 2 - 1))⁻¹]

theorem sourceLineInverse_zero (px py : ZMod P) (v : Fin 65536) :
    sourceLineInverse v 0 =
      R1ZCircleFoldMathV1.rustHalf * pointwiseInverses px py v 2 := by
  simp [sourceLineInverse, pointwiseInverses, queryGeometryValues,
    sourceLineNode_eq_stored, R1ZCircleFoldMathV1.rustHalf_eq_inv, mul_comm]

theorem sourceLineInverse_one (px py : ZMod P) (v : Fin 65536) :
    sourceLineInverse v 1 =
      -(R1ZCircleFoldMathV1.rustHalf * pointwiseInverses px py v 3) := by
  simp [sourceLineInverse, pointwiseInverses, queryGeometryValues,
    sourceLineNode_eq_stored, R1ZCircleFoldMathV1.rustHalf_eq_inv, mul_comm]

theorem sourceLineInverse_two (px py : ZMod P) (v : Fin 65536) :
    sourceLineInverse v 2 =
      R1ZCircleFoldMathV1.rustHalf * pointwiseInverses px py v 4 := by
  simp [sourceLineInverse, pointwiseInverses, queryGeometryValues,
    sourceLineNode_eq_stored, R1ZCircleFoldMathV1.rustHalf_eq_inv, mul_comm]

theorem sourceLineFold_queryGeometry {K : Type*} [Field K] [Algebra (ZMod P) K]
    (alpha : K) (a : Fin 4 → K) (px py : ZMod P) (v : Fin 65536) :
    R1ZCircleFoldMathV1.sourceLineFold alpha a
        (pointwiseInverses px py v 2) (pointwiseInverses px py v 3)
        (pointwiseInverses px py v 4) =
      AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
        (algebraMap (ZMod P) K (sourceLineInverse v 0))
        (algebraMap (ZMod P) K (sourceLineInverse v 1))
        (algebraMap (ZMod P) K (sourceLineInverse v 2)) a := by
  have h := R1ZCircleFoldMathV1.sourceLineFold_eq_model alpha a
    (pointwiseInverses px py v 2) (pointwiseInverses px py v 3)
    (pointwiseInverses px py v 4)
  rw [h, sourceLineInverse_zero px py v, sourceLineInverse_one px py v,
    sourceLineInverse_two px py v, map_neg]

#print axioms sourceLineNode_eq_stored
#print axioms queryGeometryValues_lineZ
#print axioms sourceLineFold_queryGeometry

end R1ZQueryGeometryValuesV1
