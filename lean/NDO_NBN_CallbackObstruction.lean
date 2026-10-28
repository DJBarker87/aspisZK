import NDO_NBK_DeployedCallbackSelection
set_option autoImplicit false
namespace NBN_CallbackObstruction
open Aeneas Aeneas.Std Result
open AspisR1

/-- Selection alone cannot determine the frozen getter's value. -/
theorem registry_unconstrained {F E : Type} (c : DrvC_Installation.Configuration F E)
    (r : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) :
    ∃ cFalse cTrue : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk cFalse).op25 r = ok false ∧
      (DrvC_Installation.sdk cTrue).op25 r = ok true := by
  exact ⟨{c with adapter := {c.adapter with op25 := fun _ => ok false}},
    {c with adapter := {c.adapter with op25 := fun _ => ok true}},rfl,rfl⟩

/-- No universally quantified adapter can be given a fixed op25 law from selection. -/
theorem no_fixed_registry_law {F E : Type} (c : DrvC_Installation.Configuration F E)
    (r : AdapterRw.aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1)
    (expected : Bool) :
    ¬ (∀ d : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk d).op25 r = ok expected) := by
  intro h
  obtain ⟨cf,ct,hf,ht⟩ := registry_unconstrained c r
  have ef : false = expected := Result.ok.inj (hf.symm.trans (h cf))
  have et : true = expected := Result.ok.inj (ht.symm.trans (h ct))
  cases ef.trans et.symm

#print axioms registry_unconstrained
#print axioms no_fixed_registry_law
end NBN_CallbackObstruction
