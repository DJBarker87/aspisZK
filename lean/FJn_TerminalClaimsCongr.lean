import R0P.SemDecision
set_option autoImplicit false
namespace AspisR1.FJn_TerminalClaimsCongr
variable {K : Type} [Field K]
attribute [local irreducible] R0P.SemSource.laneAt R0P.SemSource.eqValue R0P.SemSource.selAt
/-- Only the original three16-column openings and H1 are consumed by this body. -/
theorem value (p : R0P.Public K) (lambda chi theta mu : K) (zc point : Fin 10 → K)
    {F : Subfield K} (B : R0P.PackBasis F) (y y' : Fin 3 → Fin 29 → K)
    (cells : ∀ j : Fin 3,∀ i : Fin 16,y j (Fin.castLE (by omega) i)=y' j (Fin.castLE (by omega) i))
    (helper : y 0 26=y' 0 26) :
    R0P.SemSource.terminalValue p lambda chi theta mu zc B y point=
      R0P.SemSource.terminalValue p lambda chi theta mu zc B y' point := by
  have os : (⟨fun i=>y 0 (Fin.castLE (by omega) i),fun i=>y 1 (Fin.castLE (by omega) i),
    fun i=>y 2 (Fin.castLE (by omega) i)⟩ : R0P.Openings K)=
      ⟨fun i=>y' 0 (Fin.castLE (by omega) i),fun i=>y' 1 (Fin.castLE (by omega) i),
       fun i=>y' 2 (Fin.castLE (by omega) i)⟩ := by
    congr 1 <;> funext i
    · exact cells 0 i
    · exact cells 1 i
    · exact cells 2 i
  unfold R0P.SemSource.terminalValue
  rw [os,helper]
#print axioms value
end AspisR1.FJn_TerminalClaimsCongr
