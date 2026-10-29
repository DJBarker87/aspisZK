import R1Z.PV_RunJoin_NativeResidual62
import R1Z.PV_RunJoin_CircleUnit62
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleGoal62
open Aeneas Aeneas.Std Result ProverRwFull

def wanted (block : Array U8 32#usize) : Prop :=
    ((R0P.SemSource.circleSample1 (AspisV8R19.SqueezeOracleBridge.decodeState block)).val).1^2+
    ((R0P.SemSource.circleSample1 (AspisV8R19.SqueezeOracleBridge.decodeState block)).val).2^2=1

set_option pp.all true in
#print wanted
set_option pp.all true in
#print PV_RunJoin_CircleUnit62.second

theorem match_unit (block : Array U8 32#usize) : wanted block := PV_RunJoin_CircleUnit62.second block
#print axioms wanted
#print axioms match_unit
end R1Z.PV_RunJoin_CircleGoal62
