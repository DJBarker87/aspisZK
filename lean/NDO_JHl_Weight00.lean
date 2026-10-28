import NDO_JHl_WeightFormula
import RPt_JFq_Weights00
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_Weight00
open AspisV8R15.ExactTowerBase AspisCircleTensorBinding
open JHl_WeightFormula JHl_SumField

theorem source : totalAt 10 0=CheckpointBytes5Output.ofK JFq_Weight00.scalar := by
  simp only [totalAt,contribution,node,show (0 : Nat)<10 from by decide,
    show (1 : Nat)<10 from by decide,show (2 : Nat)<10 from by decide,
    show (3 : Nat)<10 from by decide,show (4 : Nat)<10 from by decide,
    show (5 : Nat)<10 from by decide,show (6 : Nat)<10 from by decide,
    show (7 : Nat)<10 from by decide,show (8 : Nat)<10 from by decide,
    show (9 : Nat)<10 from by decide,dif_pos]
  have basis (x : M31Exact) : naturalLineValue x 0=1 := by
    simp [naturalLineValue,Nat.bitIndices]
  simp only [basis,scalar,JHk_RhsFacts.power]
  change (0 : K)+1+JHk_Rhs00.power+JHk_Rhs01.power+JHk_Rhs02.power+JHk_Rhs03.power+
    JHk_Rhs04.power+JHk_Rhs05.power+JHk_Rhs06.power+JHk_Rhs07.power+JHk_Rhs08.power=_
  unfold JHk_Rhs00.power JHk_Rhs01.power JHk_Rhs02.power JHk_Rhs03.power JHk_Rhs04.power
    JHk_Rhs05.power JHk_Rhs06.power JHk_Rhs07.power JHk_Rhs08.power
  ext <;> norm_num [qm31R,M31Exact,P] <;> decide
#print axioms source
end AspisR1.JHl_Weight00
end
