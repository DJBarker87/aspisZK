import NID_ResumeFields
set_option autoImplicit false
noncomputable section
namespace NID_ResumeCallerDomain
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 NID_ResumeCanonical

theorem power (q : aspis_core.field.QM31) (canon : KCanonical q) :
 NBF_PowerStep.Canonical q := by
 intro j
 fin_cases j
 · exact canon.1
 · exact canon.2.1
 · exact canon.2.2.1
 · exact canon.2.2.2

theorem wide (q : aspis_core.field.wide_exact.WideExact) (canon : ECanonical q) :
 NBO_TailDomain.WideCanonical q := ⟨power q.c0 canon.1,power q.c1 canon.2⟩

theorem gamma (q : aspis_core.field.wide_exact.WideExact) (canon : ECanonical q) :
 NFN_LPi_FieldValues.canonE (FIo_Install.toE q) := by
 exact ⟨⟨⟨canon.1.1,canon.1.2.1⟩,⟨canon.1.2.2.1,canon.1.2.2.2⟩⟩,
  ⟨⟨canon.2.1,canon.2.2.1⟩,⟨canon.2.2.2.1,canon.2.2.2.2⟩⟩⟩

#print axioms power
#print axioms wide
#print axioms gamma
end NID_ResumeCallerDomain
