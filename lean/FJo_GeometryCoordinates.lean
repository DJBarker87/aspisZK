import FJl_CircleGeometry
import R1FirstFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_GeometryCoordinates
open AspisWide.FinalEncoder
open AspisCircleGroupOrder
variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod P) E]
theorem x (u : Fin 262144) :
    algebraMap (ZMod P) E ((Port5Q1_Domain.words u.val)[0]?.getD 0)=exactCircleX u := by
  have idx : Port5Q1_Domain.index u.val=u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
  simp only [Port5Q1_Domain.words,List.getElem?_cons_zero,Option.getD_some,idx,
    FoldStoredGeometry.fibre_eq_stored]
  rfl
theorem y (u : Fin 262144) :
    algebraMap (ZMod P) E ((Port5Q1_Domain.words u.val)[1]?.getD 0)=exactCircleY u := by
  have idx : Port5Q1_Domain.index u.val=u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
  simp only [Port5Q1_Domain.words,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,idx,
    FoldStoredGeometry.fibre_eq_stored]
  rfl
#print axioms x
#print axioms y
end AspisR1.FJo_GeometryCoordinates
end
