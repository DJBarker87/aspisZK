import R1Z.PV_RunJoin_CommonRecord51
import R1Z.PhaseSamplerParserBin
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommonChallenges51
open R0Z R0Z.FsStatement R1Z.GamesR1 R1Z.TranscriptR1
local notation "K" => AspisWideTower.WideExact
variable {CH Aux : Type}

theorem opening (W : R1Wire K CH Aux) (tr : TRead → OracleAnswer) (i : Fin 4) :
    (chOf (PhaseSamplerParserBin.wireData W) tr).opening i=
      PhaseSamplerParserBin.openingScalar i (tr (.sqO i)) := rfl

theorem semantic (W : R1Wire K CH Aux) (tr : TRead → OracleAnswer) (i : Fin 25) :
    (chOf (PhaseSamplerParserBin.wireData W) tr).sem i=
      PhaseSamplerParserBin.scalar (tr (.sqS ⟨i.val,by omega⟩)) := rfl

theorem alpha (W : R1Wire K CH Aux) (tr : TRead → OracleAnswer) (i : Fin 10) :
    HonestView.alpha (chOf (PhaseSamplerParserBin.wireData W) tr) i=
      PhaseSamplerParserBin.scalar (tr (.sqS ⟨15+i.val,by omega⟩)) := rfl

theorem circle (W : R1Wire K CH Aux) (tr : TRead → OracleAnswer) (i : Fin 2) :
    (chOf (PhaseSamplerParserBin.wireData W) tr).circle i=
      PhaseSamplerParserBin.circle i (tr (.sqS ⟨25+i.val,by omega⟩)) := rfl
#print axioms opening
#print axioms semantic
#print axioms alpha
#print axioms circle
end R1Z.PV_RunJoin_CommonChallenges51
