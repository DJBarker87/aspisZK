import SAQ_LineSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAQ_LineArrays
open Aeneas Aeneas.Std Result
abbrev FP := ZMod AspisCircleGroupOrder.P

theorem four {T : Type} (a : Array T 4#usize) :
    ∃ a0 a1 a2 a3, a=Array.make 4#usize [a0,a1,a2,a3] := by
  obtain ⟨a0,a1,a2,a3,h⟩ := List.length_eq_four.mp a.property
  exact ⟨a0,a1,a2,a3,Subtype.ext h⟩

theorem five {T : Type} (a : Array T 5#usize) :
    ∃ a0 a1 a2 a3 a4, a=Array.make 5#usize [a0,a1,a2,a3,a4] := by
  obtain ⟨a0,a1,a2,a3,a4,h⟩ := List.length_eq_five.mp a.property
  exact ⟨a0,a1,a2,a3,a4,Subtype.ext h⟩

theorem source_eq_inverses {K : Type} [Field K] [Algebra FP K]
    (alpha : K) (v : Fin 4 → K) (ix iy iz : FP) :
    R1ZCircleFoldMathV1.sourceLineFold alpha v ix iy iz =
      FoldRuntimeAlgebra.lineWithInverses alpha (algebraMap FP K ix)
        (algebraMap FP K iy) (algebraMap FP K iz) v := by
  have quarter : algebraMap FP K R1ZCircleFoldMathV1.rustQuarter=(4:K)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have h := congrArg (algebraMap FP K) R1ZCircleFoldMathV1.four_mul_rustQuarter
    rwa [map_mul,map_one,map_ofNat] at h
  simp only [R1ZCircleFoldMathV1.sourceLineFold,FoldRuntimeAlgebra.lineWithInverses,
    map_mul,quarter,R1ZCircleFoldMathV1.algebraMap_rustHalf]

#print axioms four
#print axioms five
#print axioms source_eq_inverses
end AspisR1.SAQ_LineArrays
end
