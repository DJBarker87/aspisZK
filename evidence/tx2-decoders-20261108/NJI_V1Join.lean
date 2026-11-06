import NJI_V1Models
set_option autoImplicit false
noncomputable section
namespace NJI_V1Join
open Aeneas Aeneas.Std Result NJI_V1Carrier

def registry (r : CR) : Result (core.result.Result Unit CF) := do
 let reply ← NJI_V1Models.registry (from_registry r)
 ok (port reply)

def entry (r : CE) : Result (core.result.Result Unit CF) := do
 let reply ← NJI_V1Models.entry (from_entry r)
 ok (port reply)

/-- Complete emitted Result transported to the canonical cohort record, every input. -/
theorem registry_source (r : R) :
 (do let reply ← NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_v1 r
     ok (port reply)) = registry (NJI_V1Carrier.registry r) := by
 unfold registry
 rw [registry_roundtrip,NJI_V1Models.registry_source]

/-- No decoded-success premise: every status and malformed binding is included. -/
theorem entry_source (r : E) :
 (do let reply ← NJI_Extracted.aspis_statement.pool_v1.verifier_registry.validate_verifier_registry_entry_v1 r
     ok (port reply)) = entry (NJI_V1Carrier.entry r) := by
 unfold entry
 rw [entry_roundtrip,NJI_V1Models.entry_source]

/-- The port is total on caller records; no hidden representability restriction. -/
theorem registry_domain (r : CR) : NJI_V1Carrier.registry (from_registry r)=r := registry_surjective r

theorem entry_domain (r : CE) : NJI_V1Carrier.entry (from_entry r)=r := entry_surjective r

#print registry_source
#print entry_source
#print axioms registry_source
#print axioms entry_source
#print axioms registry_domain
#print axioms entry_domain
end NJI_V1Join
