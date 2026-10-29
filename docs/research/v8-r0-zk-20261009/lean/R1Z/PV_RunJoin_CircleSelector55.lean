import R1Z.PhaseSamplerParserBin
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleSelector55

theorem first (b : R0Z.FsStatement.OracleAnswer) :
    PhaseSamplerParserBin.circle ⟨0,by decide⟩ b=PhaseCircleBlocksBin.first b := by
  unfold PhaseSamplerParserBin.circle PhaseCircleBlocksBin.select
  rw [dif_pos (show (⟨0,by decide⟩ : Fin 2).val=0 from rfl)]

theorem second (b : R0Z.FsStatement.OracleAnswer) :
    PhaseSamplerParserBin.circle ⟨1,by decide⟩ b=
      R0P.SemSource.circleSample1 (fun i => (b i).toFin) := by
  unfold PhaseSamplerParserBin.circle PhaseCircleBlocksBin.select
  rw [dif_neg (show ¬(⟨1,by decide⟩ : Fin 2).val=0 by decide)]
#print axioms first
#print axioms second
end R1Z.PV_RunJoin_CircleSelector55
