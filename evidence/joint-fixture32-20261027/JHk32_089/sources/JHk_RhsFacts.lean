import JHk_Rhs00
import JHk_Rhs01
import JHk_Rhs02
import JHk_Rhs03
import JHk_Rhs04
import JHk_Rhs05
import JHk_Rhs06
import JHk_Rhs07
import JHk_Rhs08
import JHk_Rhs09
import JHk_LineValues
set_option autoImplicit false
namespace AspisR1.JHk_RhsFacts
def rhs (n : Nat) : AspisWideTower.WideExact := match n with
  | 0 => 0
  | 1 => JHk_Rhs00.rhs
  | 2 => JHk_Rhs01.rhs
  | 3 => JHk_Rhs02.rhs
  | 4 => JHk_Rhs03.rhs
  | 5 => JHk_Rhs04.rhs
  | 6 => JHk_Rhs05.rhs
  | 7 => JHk_Rhs06.rhs
  | 8 => JHk_Rhs07.rhs
  | 9 => JHk_Rhs08.rhs
  | _ => JHk_Rhs09.rhs
def power (n : Nat) : OraclePortCheckpointAbiC5.K := match n with
  | 0 => 1
  | 1 => JHk_Rhs00.power
  | 2 => JHk_Rhs01.power
  | 3 => JHk_Rhs02.power
  | 4 => JHk_Rhs03.power
  | 5 => JHk_Rhs04.power
  | 6 => JHk_Rhs05.power
  | 7 => JHk_Rhs06.power
  | 8 => JHk_Rhs07.power
  | 9 => JHk_Rhs08.power
  | _ => JHk_Rhs09.power
theorem rhs_step (i : Fin 10) :
    rhs (i.val+1)=rhs i.val+LiteralOpeningView.eK (power i.val)*JHk_LineValues.value i := by
  fin_cases i
  · exact JHk_Rhs00.rhs_step.symm
  · exact JHk_Rhs01.rhs_step.symm
  · exact JHk_Rhs02.rhs_step.symm
  · exact JHk_Rhs03.rhs_step.symm
  · exact JHk_Rhs04.rhs_step.symm
  · exact JHk_Rhs05.rhs_step.symm
  · exact JHk_Rhs06.rhs_step.symm
  · exact JHk_Rhs07.rhs_step.symm
  · exact JHk_Rhs08.rhs_step.symm
  · exact JHk_Rhs09.rhs_step.symm
#print axioms rhs_step
theorem power_step (i : Fin 10) :
    power (i.val+1)=power i.val*CheckpointBytes5Output.ofK JFq_Rho.scalar := by
  fin_cases i
  · exact JHk_Rhs00.power_step.symm
  · exact JHk_Rhs01.power_step.symm
  · exact JHk_Rhs02.power_step.symm
  · exact JHk_Rhs03.power_step.symm
  · exact JHk_Rhs04.power_step.symm
  · exact JHk_Rhs05.power_step.symm
  · exact JHk_Rhs06.power_step.symm
  · exact JHk_Rhs07.power_step.symm
  · exact JHk_Rhs08.power_step.symm
  · exact JHk_Rhs09.power_step.symm
#print axioms power_step
theorem retained : rhs 10=CheckpointBytes5Output.ofE JFq_Rhs.scalar := JHk_Rhs09.retained
#print axioms retained
end AspisR1.JHk_RhsFacts
