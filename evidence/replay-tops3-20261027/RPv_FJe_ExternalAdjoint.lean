import RPv_FJe_PackingLinear
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_ExternalAdjoint
variable {K : Type} [Field K]
def lane (g j : Fin 4) : Fin 16 := ⟨4*g.val+j.val,by omega⟩
def localRows (s : Fin 16 → K) (g : Fin 4) : Fin 4 → K :=
  R0P.poseidonMat4 (fun j=>s (lane g j))
def packedLocal (i u : K) (s : Fin 16 → K) (g : Fin 4) : K :=
  R0P.poseidonPackingFormula i u (localRows s g)
def reference (i u : K) (s : Fin 16 → K) (g : Fin 4) : K :=
  packedLocal i u s g + ((((0+packedLocal i u s 0)+packedLocal i u s 1)+
    packedLocal i u s 2)+packedLocal i u s 3)
/-- The P6 reference's final map is the packed literal external matrix. -/
theorem value (i u : K) (s : Fin 16 → K) (g : Fin 4) :
    reference i u s g = R0P.poseidonPackingFormula i u
      (fun j=>R0P.poseidonExternalLinear s (lane g j)) := by
  have hc (j : Fin 4) : R0P.poseidonExternalLinear s (lane g j)=
      localRows s g j+((((0+localRows s 0 j)+localRows s 1 j)+localRows s 2 j)+localRows s 3 j) := by
    have hg := g.isLt
    have hj := j.isLt
    have hdiv : (4*g.val+j.val)/4=g.val := by omega
    have hmod : (4*g.val+j.val)%4=j.val := by omega
    simp only [R0P.poseidonExternalLinear,lane,hdiv,hmod]
    rfl
  simp_rw [hc]
  unfold reference packedLocal R0P.poseidonPackingFormula
  ring
#print axioms value
end AspisR1.FJe_ExternalAdjoint
end
