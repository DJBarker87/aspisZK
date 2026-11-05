import NIS_GuardPrefix
import NHY_RegistryPrimitives
set_option autoImplicit false
noncomputable section
namespace NIJ_AuthGuardsV2
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1.verifier_registry
attribute [local instance] Classical.propDecidable
abbrev Key := Array U8 32#usize

/-- The actual decoded V2 registry's eight comparisons, in source order.
The two flag replies are primitive child results, not enclosing success. -/
def registry (r : VerifierRegistryV2) (authority binding : Key)
 (master program loader programdata : Key) (immutable paused : Bool) : List Bool :=
 [decide (r.pool≠master),decide (r.authority≠authority),
  decide (r.policy_binding≠binding),decide (r.registry_program≠program),
  decide (r.loader_program≠loader),decide (r.programdata_address≠programdata),
  !immutable,paused]

/-- Complete V2 entry comparison sequence. Active-slot is a named child
reply; its source packet remains independently required. -/
def entry (r : VerifierRegistryEntryV2)
 (master binding verifier profile release loader programdata : Key)
 (version : U8) (active : Bool) : List Bool :=
 [decide (r.pool≠master),decide (r.policy_binding≠binding),
  decide (r.verifier_program≠verifier),decide (r.profile_binding≠profile),
  decide (r.release_binding≠release),decide (r.statement_version≠version),
  decide (r.loader_program≠loader),decide (r.programdata_address≠programdata),
  decide (r.expected_upgrade_authority≠Array.repeat 32#usize 0#u8),!active]

theorem registry_trace (r : VerifierRegistryV2) (authority binding master program loader programdata : Key)
 (immutable paused : Bool) :
 (NIJ_GuardPrefix.visit 0 (registry r authority binding master program loader programdata immutable paused)).2=
 List.range' 0 (NIJ_GuardPrefix.count (registry r authority binding master program loader programdata immutable paused)) :=
 NIJ_GuardPrefix.trace _ _

theorem entry_trace (r : VerifierRegistryEntryV2)
 (master binding verifier profile release loader programdata : Key) (version : U8) (active : Bool) :
 (NIJ_GuardPrefix.visit 0 (entry r master binding verifier profile release loader programdata version active)).2=
 List.range' 0 (NIJ_GuardPrefix.count (entry r master binding verifier profile release loader programdata version active)) :=
 NIJ_GuardPrefix.trace _ _

theorem registry_domain (r : VerifierRegistryV2) (authority binding master program loader programdata : Key)
 (immutable paused : Bool) :
 NIJ_GuardPrefix.count (registry r authority binding master program loader programdata immutable paused)≤8 :=
 NIJ_GuardPrefix.bound _

theorem entry_domain (r : VerifierRegistryEntryV2)
 (master binding verifier profile release loader programdata : Key) (version : U8) (active : Bool) :
 NIJ_GuardPrefix.count (entry r master binding verifier profile release loader programdata version active)≤10 :=
 NIJ_GuardPrefix.bound _

#print axioms registry_trace
#print axioms entry_trace
#print axioms registry_domain
#print axioms entry_domain
end NIJ_AuthGuardsV2
