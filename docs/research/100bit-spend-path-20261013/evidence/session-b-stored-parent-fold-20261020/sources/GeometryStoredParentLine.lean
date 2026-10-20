import GeometryStoredNonzero
import R1ZQueryGeometryValuesV6
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
open R1ZQueryGeometryValuesV1

def storedParent {q : U32} (g : StoredGeometryPoint q) : Fin 65536 :=
  sourceParent ⟨g.u.val,g.hu⟩

theorem storedLineX_parent {q : U32} (g : StoredGeometryPoint q) :
    storedLineX g = AspisV7ExactOneFoldDomains.storedFirstLineX18
      (AspisV5ComponentCConcreteFoldLinearity.childIndex (storedParent g) 0) := by
  apply congrArg AspisV7ExactOneFoldDomains.storedFirstLineX18
  apply Fin.ext
  exact g.ixIndex.trans (sourceParent_child0_val ⟨g.u.val,g.hu⟩).symm

theorem storedLineY_parent {q : U32} (g : StoredGeometryPoint q) :
    storedLineY g = AspisV7ExactOneFoldDomains.storedFirstLineX18
      (AspisV5ComponentCConcreteFoldLinearity.childIndex (storedParent g) 3) := by
  apply congrArg AspisV7ExactOneFoldDomains.storedFirstLineX18
  apply Fin.ext
  exact g.iyIndex.trans (sourceParent_child3_val ⟨g.u.val,g.hu⟩).symm

theorem stored_line_inverse_zero {q : U32} (g : StoredGeometryPoint q) :
    sourceLineInverse (storedParent g) 0 = R1ZCircleFoldMathV1.rustHalf * (storedLineX g)⁻¹ := by
  have h := sourceLineInverse_zero (0 : ZMod AspisR1FoldInverses.Refinement.P) 0 (storedParent g)
  simp only [pointwiseInverses, queryGeometryValues_lineX] at h
  rw [← storedLineX_parent g] at h
  exact h

theorem stored_line_inverse_one {q : U32} (g : StoredGeometryPoint q) :
    sourceLineInverse (storedParent g) 1 = -(R1ZCircleFoldMathV1.rustHalf * (storedLineY g)⁻¹) := by
  have h := sourceLineInverse_one (0 : ZMod AspisR1FoldInverses.Refinement.P) 0 (storedParent g)
  simp only [pointwiseInverses, queryGeometryValues_lineY] at h
  rw [← storedLineY_parent g] at h
  exact h

theorem stored_line_inverse_two {q : U32} (g : StoredGeometryPoint q) :
    sourceLineInverse (storedParent g) 2 = R1ZCircleFoldMathV1.rustHalf * (storedLineZ g)⁻¹ := by
  have h := sourceLineInverse_two (0 : ZMod AspisR1FoldInverses.Refinement.P) 0 (storedParent g)
  simp only [pointwiseInverses, queryGeometryValues_lineZ] at h
  rw [← storedLineX_parent g] at h
  exact h

#print axioms storedLineX_parent
#print axioms storedLineY_parent
#print axioms stored_line_inverse_zero
#print axioms stored_line_inverse_one
#print axioms stored_line_inverse_two
end AspisR1CurrentWide.Proof
