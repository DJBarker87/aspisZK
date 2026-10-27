import RPv_PoseidonResidualFieldTransport
set_option autoImplicit false
namespace AspisR1.FJk_ResidualNaturality
variable {K L : Type} [Field K] [Field L]
attribute [local irreducible] R0P.poseidonScalarResidual R0P.g2SumHigh R0P.g2Low
/-- Naturality with the model's selector marginals, without concrete native types. -/
theorem value (f : K →+* L) (o : R0P.Openings K) (sel : R0P.Sel K) (lane : Fin 16) :
    f (R0P.poseidonScalarResidual o (R0P.g2SumHigh sel 0 57 (by decide)) (R0P.g2Low sel) lane)=
    R0P.poseidonScalarResidual (ValueFamilyFieldTransport.mapOpenings f o)
      (R0P.g2SumHigh (fun i=>f (sel i)) 0 57 (by decide))
      (R0P.g2Low (fun i=>f (sel i))) lane := by
  have h := PoseidonResidualFieldTransport.map_scalarResidual f o
    (R0P.g2SumHigh sel 0 57 (by decide)) (R0P.g2Low sel) lane
  have hb := PathFamilyFieldTransport.map_sumHigh f sel 0 57 (by decide)
  have hl : PoseidonMap.mapState f (R0P.g2Low sel)=R0P.g2Low (fun i=>f (sel i)) := by
    funext i
    exact PathFamilyFieldTransport.map_low f sel i
  exact h.trans (congrArg₂ (fun b l=>R0P.poseidonScalarResidual
    (ValueFamilyFieldTransport.mapOpenings f o) b l lane) hb hl)
#print axioms value
end AspisR1.FJk_ResidualNaturality
