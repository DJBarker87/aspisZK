import NBL_PassConstruct
set_option autoImplicit false
namespace AspisR1.NMP_PassCertificate179
open Aeneas Aeneas.Std Result
open SamplerMachineBounds SamplerWord SamplerWordPass
/-- Select the canonical machine-run certificate from the existing symbolic construction. The native
step correspondence is the already CLOSED LPk_Step.machine_step law. No whole
sampler equality, concrete long reduction, or hash success is a premise. -/
theorem source (r : UInt64) (xs : List UInt32) (bounded : r.toNat<P) :
 LPk_Induction.Pass r xs (machineProcess r xs).1 (machineProcess r xs).2 := by
 obtain ⟨out,qs,trace⟩ := NBL_PassConstruct.pass r xs bounded
 have same := LPk_Induction.pass_join trace bounded
 rw [←same]
 exact trace
#print axioms source
end AspisR1.NMP_PassCertificate179
