import RPz7_F3M_CircleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_CircleScope
open AspisR1PublicPreparation

theorem install_eq (B : FinishModel.Boundaries) (circle : B.circle=F3M_CircleSource.source) :
    F3M_CircleSource.install B=B := by
  cases B
  simp_all only [F3M_CircleSource.install]

theorem necessary (B : FinishModel.Boundaries) (same : F3M_CircleSource.install B=B) :
    B.circle=F3M_CircleSource.source := by
  exact (congrArg FinishModel.Boundaries.circle same).symm

theorem characterization (B : FinishModel.Boundaries) :
    F3M_CircleSource.install B=B ↔ B.circle=F3M_CircleSource.source :=
  ⟨necessary B,install_eq B⟩

#print axioms install_eq
#print axioms necessary
#print axioms characterization
end AspisR1.F3Q_CircleScope
end
