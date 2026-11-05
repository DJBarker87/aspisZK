import NIJ_GuardPrefix
import NHY_RegistryPrimitives
set_option autoImplicit false
noncomputable section
namespace NIJ_AuthGuardsV1
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1.verifier_registry
attribute [local instance] Classical.propDecidable
abbrev Key := Array U8 32#usize

/-- The actual decoded V1 registry's five comparisons, in source order.
The two flag replies are primitive child results, not enclosing success. -/
def registry (r : VerifierRegistryV1) (authority binding : Key)
 (master program loader programdata : Key) (immutable paused : Bool) : List Bool :=
 [decide (r.pool≠master),decide (r.authority≠authority),
  decide (r.policy_binding≠binding),!immutable,paused]

/-- Complete V1 entry comparison sequence. Active-slot is a named child
reply; its source packet remains independently required. -/
def entry (r : VerifierRegistryEntryV1)
 (master binding verifier profile release loader programdata : Key)
 (version : U8) (active : Bool) : List Bool :=
 [decide (r.pool≠master),decide (r.policy_binding≠binding),
  decide (r.verifier_program≠verifier),decide (r.profile_binding≠profile),
  decide (r.release_binding≠release),decide (r.statement_version≠version),!active]

theorem registry_trace (r : VerifierRegistryV1) (authority binding master program loader programdata : Key)
 (immutable paused : Bool) :
 (NIJ_GuardPrefix.visit 0 (registry r authority binding master program loader programdata immutable paused)).2=
 List.range' 0 (NIJ_GuardPrefix.count (registry r authority binding master program loader programdata immutable paused)) :=
 NIJ_GuardPrefix.trace _ _

theorem entry_trace (r : VerifierRegistryEntryV1)
 (master binding verifier profile release loader programdata : Key) (version : U8) (active : Bool) :
 (NIJ_GuardPrefix.visit 0 (entry r master binding verifier profile release loader programdata version active)).2=
 List.range' 0 (NIJ_GuardPrefix.count (entry r master binding verifier profile release loader programdata version active)) :=
 NIJ_GuardPrefix.trace _ _

theorem registry_domain (r : VerifierRegistryV1) (authority binding master program loader programdata : Key)
 (immutable paused : Bool) :
 NIJ_GuardPrefix.count (registry r authority binding master program loader programdata immutable paused)≤5 :=
 NIJ_GuardPrefix.bound _

theorem entry_domain (r : VerifierRegistryEntryV1)
 (master binding verifier profile release loader programdata : Key) (version : U8) (active : Bool) :
 NIJ_GuardPrefix.count (entry r master binding verifier profile release loader programdata version active)≤7 :=
 NIJ_GuardPrefix.bound _

#print axioms registry_trace
#print axioms entry_trace
#print axioms registry_domain
#print axioms entry_domain
end NIJ_AuthGuardsV1
