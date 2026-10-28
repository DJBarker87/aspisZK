import NDO_JHl_Z0X
import NDO_JHl_Z0Y
import NDO_JHl_Z1X
import NDO_JHl_Z1Y
import NDO_JHl_PreparedSemantic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_ZPoints
open AspisV8R15.ExactTowerBase AspisV8R19.SamplerCirclePolicy
open AspisV8R15.CircleChord
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition

theorem point0 : point JFu_CircleParameters.t25=(JHl_Z0X.value,JHl_Z0Y.value) := by
  have hd := outside_has_denominator _ JFu_CircleParameters.outside25
  apply Prod.ext
  · change (1-JFu_CircleParameters.t25^2)/(1+JFu_CircleParameters.t25^2)=_
    apply Eq.symm
    apply (eq_div_iff hd).mpr
    rw [JHl_Z0Square.den,JHl_Z0X.source,JHl_Z0Square.source]
  · change (2*JFu_CircleParameters.t25)/(1+JFu_CircleParameters.t25^2)=_
    apply Eq.symm
    apply (eq_div_iff hd).mpr
    rw [JHl_Z0Square.den,JHl_Z0Y.source]
#print axioms point0

theorem point1 : point JFu_CircleParameters.t26=(JHl_Z1X.value,JHl_Z1Y.value) := by
  have hd := outside_has_denominator _ JFu_CircleParameters.outside26
  apply Prod.ext
  · change (1-JFu_CircleParameters.t26^2)/(1+JFu_CircleParameters.t26^2)=_
    apply Eq.symm
    apply (eq_div_iff hd).mpr
    rw [JHl_Z1Square.den,JHl_Z1X.source,JHl_Z1Square.source]
  · change (2*JFu_CircleParameters.t26)/(1+JFu_CircleParameters.t26^2)=_
    apply Eq.symm
    apply (eq_div_iff hd).mpr
    rw [JHl_Z1Square.den,JHl_Z1Y.source]
#print axioms point1

theorem native0 : (⟨Tx1Q_Carriers.k (currentPoint JFu_CircleExact.z0).x,
      Tx1Q_Carriers.k (currentPoint JFu_CircleExact.z0).y⟩ : AspisR1Stage2.aspis_core.circle.SecureCirclePoint)=
    (⟨JFq_Z0.scalar,JFq_Z1.scalar⟩ : AspisR1Stage2.aspis_core.circle.SecureCirclePoint) := by
  unfold JFu_CircleExact.z0
  rw [point0]
  rfl
#print axioms native0

theorem native1 : (⟨Tx1Q_Carriers.k (currentPoint JFu_CircleExact.z1).x,
      Tx1Q_Carriers.k (currentPoint JFu_CircleExact.z1).y⟩ : AspisR1Stage2.aspis_core.circle.SecureCirclePoint)=
    (⟨JFq_Z2.scalar,JFq_Z3.scalar⟩ : AspisR1Stage2.aspis_core.circle.SecureCirclePoint) := by
  unfold JFu_CircleExact.z1
  rw [point1]
  rfl
#print axioms native1
end AspisR1.JHl_ZPoints
end
