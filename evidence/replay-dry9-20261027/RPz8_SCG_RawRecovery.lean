import RPz8_SCF_Recovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_RawRecovery
open OraclePortRefineJoin

/-- Standalone source/model evaluation equality supplies recovery equality
only for views built from those equal evaluations. The physical account view
is a third carrier and does not occur in this theorem. -/
theorem same (source model : RawCutProverCompiler.RunView) (equal : source = model) :
    RecoveredInputAgreement source model := by
  subst model
  exact ⟨rfl,rfl,rfl⟩

/-- The exact recovery interface composes; no order or sublist surrogate is
silently substituted for its three executable equalities. -/
theorem trans (physical source model : RawCutProverCompiler.RunView)
    (first : RecoveredInputAgreement physical source)
    (second : RecoveredInputAgreement source model) :
    RecoveredInputAgreement physical model :=
  ⟨first.decoded_public.trans second.decoded_public,
   first.initial.trans second.initial,first.final.trans second.final⟩

#print axioms same
#print axioms trans
end AspisR1.SCG_RawRecovery
end
