import RPu_FJh_Base
set_option autoImplicit false
namespace AspisR1.FJh_ResidualModel
variable {K : Type} [Field K]
/-- Scalar residual interface with the three round values kept symbolic. -/
theorem value (o : R0P.Openings K) (low : Fin 16 → K) (block : K) (lane : Fin 16) :
    block*(low 0*(o.succ lane-R0P.poseidonLeadingPair o.z o.xor12 lane)+
      (low 1+low 9+low 10)*(o.succ lane-R0P.poseidonInterpolatedFullPair o.z low lane)+
      (List.ofFn (fun i : Fin 7=>low ⟨i.val+2,by omega⟩)).foldl (·+·) 0 *
        (o.succ lane-R0P.poseidonInterpolatedInternalPair o.z low lane))=
    R0P.poseidonScalarResidual o block low lane := by
  unfold R0P.poseidonScalarResidual
  simp only [List.foldl_cons,List.foldl_nil,zero_add]
#print axioms value
end AspisR1.FJh_ResidualModel
