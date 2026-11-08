import LIBC_PreparedDomain
import NHS_ProducedCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreparedFacts094
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- A returned law observation exposes only the SAME deterministic emitted
producer result. Allocation-stop alternatives never supply a Prepared value. -/
theorem emitted (input : LIBC_PreparedLaw.Args) (env : RSL.Env)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) (ev : List RSL.Event)
 (returned : LIBC_PreparedLaw.law input env ⟨.ret (.ok p,g),ev⟩) :
 NGN_Emitted.prepared NHL_PreparedScalars.actual (LIBC_PreparedLog.digest env)
  input.1 input.2.1 () input.2.2 = ok (.Ok p,g) := by
 obtain ⟨native,run,reply,_⟩ := (LIBC_PreparedLaw.returned input env (.ok p,g) ev).mp returned
 rw [LIBC_PreparedLaw.native_result] at run
 rcases native with ⟨r,scratch⟩
 cases r with
 | Err e => cases congrArg Prod.fst reply
 | Ok out =>
   have parts := Prod.mk.inj reply
   have hp := Except.ok.inj parts.1
   subst out
   have hg : g=scratch := parts.2
   rw [←hg] at run
   exact run
#print axioms emitted

/-- Canonical samplers and the produced powers are derived from that SAME
returned result; no successful independent preparation is a parent premise. -/
theorem canonical (input : LIBC_PreparedLaw.Args) (env : RSL.Env)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) (ev : List RSL.Event)
 (returned : LIBC_PreparedLaw.law input env ⟨.ret (.ok p,g),ev⟩) :
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative p.gamma) ∧
 NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative p.kappa) ∧
 (∀ x∈p.alpha.val,NFN_LPi_FieldValues.canonE (NFW_SampledDomains.toNative x)) ∧
 NBF_PowerStep.Canonical (NFW_PreparedPort.prepared p).rho ∧
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (NFW_PreparedPort.map NFW_PreparedPort.e g)) :=
 NHS_ProducedCanonical.source (LIBC_PreparedLog.digest env) input.1 input.2.1 () input.2.2 g p
  (emitted input env p g ev returned)
#print axioms canonical
end AspisR1.NNG_PreparedFacts094
