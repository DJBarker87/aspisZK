import R0P.Poseidon
set_option autoImplicit false
namespace AspisR1.FJk_PoseidonPackedAt
variable {K : Type} [Field K]
attribute [local irreducible] R0P.pack4 R0P.poseidonScalarResidual R0P.g2SumHigh R0P.g2Low
/-- A single packed-family cell; no round constants or transition is reduced. -/
theorem value {F : Subfield K} (B : R0P.PackBasis F) (pub : R0P.Public K)
    (o : R0P.Openings K) (sel : R0P.Sel K) (g : Fin 4) :
    ((R0P.poseidonPackedFamily B).residuals pub o sel).getD g.val 0 =
    R0P.pack4 B (fun j : Fin 4=>R0P.poseidonScalarResidual o
      (R0P.g2SumHigh sel 0 57 (by decide)) (R0P.g2Low sel)
      ⟨4*g.val+j.val,by omega⟩) := by
  simp only [R0P.poseidonPackedFamily,List.getD,List.getElem?_ofFn,
    dif_pos g.isLt,Option.getD_some]
#print axioms value
end AspisR1.FJk_PoseidonPackedAt
