import PoolL_AS8CRoles
import PoolL_AS8DRoles
import PoolL_AS8IRoles
import PoolL_ASDIRoles
import PoolL_ASINRoles
import PoolL_ASPFRoles
import PoolL_ASPPRoles
import PoolL_ASPTRoles
import PoolL_ASPXRoles
import PoolL_ASQ8Roles
import PoolL_ASWDRoles
import PoolL_AllocateAccepted
import PoolL_AllocateControl
import PoolL_AllocateEffects
import PoolL_AllocateReject
import PoolL_AllocateSource
import PoolL_BorrowFacts
import PoolL_BorrowSource
import PoolL_CancelPhysical
import PoolL_CanonicalAccepted
import PoolL_CanonicalControl
import PoolL_CanonicalReach
import PoolL_CanonicalRoleAccepted
import PoolL_CanonicalRoleControl
import PoolL_CanonicalRoleEffects
import PoolL_CanonicalRoleReject
import PoolL_CanonicalRoleSource
import PoolL_CanonicalSource
import PoolL_CloseAccepted
import PoolL_CloseControl
import PoolL_CloseEffects
import PoolL_CloseReject
import PoolL_CloseSource
import PoolL_FreshAccepted
import PoolL_FreshControl
import PoolL_FreshLengthFacts
import PoolL_FreshLengthReject
import PoolL_FreshLengthSource
import PoolL_FreshReach
import PoolL_FreshRoleControl
import PoolL_FreshRoleEffects
import PoolL_FreshRoleReject
import PoolL_FreshRoleSource
import PoolL_FreshSource
import PoolL_LengthAccepted
import PoolL_LengthFacts
import PoolL_LengthOccupied
import PoolL_LengthSource
import PoolL_MarkerAccepted
import PoolL_MarkerControl
import PoolL_MarkerLengthFacts
import PoolL_MarkerLengthReject
import PoolL_MarkerLengthSource
import PoolL_MarkerReach
import PoolL_MarkerRoleControl
import PoolL_MarkerRoleEffects
import PoolL_MarkerRoleReject
import PoolL_MarkerRoleSource
import PoolL_MarkerSource
import PoolL_PayerAccepted
import PoolL_PayerControl
import PoolL_PayerReach
import PoolL_Physical
import PoolL_PhysicalAlias
import PoolL_PhysicalAllocate
import PoolL_PhysicalCanonical
import PoolL_PhysicalClose
import PoolL_PhysicalFresh
import PoolL_PhysicalMarker
import PoolL_PhysicalPlan
import PoolL_ProgramAccepted
import PoolL_ProgramControl
import PoolL_ProgramSource
import PoolL_RoleComposition
import PoolL_RoleReach
import PoolL_VaultAccepted
import PoolL_VaultControl
import PoolL_VaultReach
import PoolL_VaultSource
import PoolL_VerifierScopes

/- Focused audit of every new top theorem; no package/manifest replay. -/
#print axioms AspisR1.PoolL_AS8CRoles.role_frame
#print axioms AspisR1.PoolL_AS8DRoles.role_frame
#print axioms AspisR1.PoolL_AS8IRoles.role_frame
#print axioms AspisR1.PoolL_ASDIRoles.role_frame
#print axioms AspisR1.PoolL_ASINRoles.role_frame
#print axioms AspisR1.PoolL_ASPFRoles.role_frame
#print axioms AspisR1.PoolL_ASPPRoles.role_frame
#print axioms AspisR1.PoolL_ASPTRoles.role_frame
#print axioms AspisR1.PoolL_ASPXRoles.role_frame
#print axioms AspisR1.PoolL_ASQ8Roles.role_frame
#print axioms AspisR1.PoolL_ASWDRoles.role_frame
#print axioms AspisR1.PoolL_AllocateAccepted.accepted
#print axioms AspisR1.PoolL_AllocateControl.control
#print axioms AspisR1.PoolL_AllocateEffects.occupied_frame
#print axioms AspisR1.PoolL_AllocateReject.non_system
#print axioms AspisR1.PoolL_AllocateReject.nonempty
#print axioms AspisR1.PoolL_BorrowFacts.success
#print axioms AspisR1.PoolL_BorrowFacts.error
#print axioms AspisR1.PoolL_BorrowFacts.accepted
#print axioms AspisR1.PoolL_CancelPhysical.accepted_separation
#print axioms AspisR1.PoolL_CanonicalAccepted.accepted
#print axioms AspisR1.PoolL_CanonicalControl.control
#print axioms AspisR1.PoolL_CanonicalReach.reachable
#print axioms AspisR1.PoolL_CanonicalRoleAccepted.accepted
#print axioms AspisR1.PoolL_CanonicalRoleControl.control
#print axioms AspisR1.PoolL_CanonicalRoleEffects.occupied_frame
#print axioms AspisR1.PoolL_CanonicalRoleEffects.no_suffix
#print axioms AspisR1.PoolL_CanonicalRoleReject.occupied
#print axioms AspisR1.PoolL_CloseAccepted.accepted
#print axioms AspisR1.PoolL_CloseControl.control
#print axioms AspisR1.PoolL_CloseEffects.occupied_no_close
#print axioms AspisR1.PoolL_CloseReject.size_error
#print axioms AspisR1.PoolL_CloseReject.occupied
#print axioms AspisR1.PoolL_FreshAccepted.accepted
#print axioms AspisR1.PoolL_FreshControl.control
#print axioms AspisR1.PoolL_FreshLengthFacts.exact
#print axioms AspisR1.PoolL_FreshLengthReject.occupied
#print axioms AspisR1.PoolL_FreshReach.reachable
#print axioms AspisR1.PoolL_FreshRoleControl.control
#print axioms AspisR1.PoolL_FreshRoleEffects.occupied_frame
#print axioms AspisR1.PoolL_FreshRoleReject.occupied
#print axioms AspisR1.PoolL_LengthAccepted.accepted
#print axioms AspisR1.PoolL_LengthFacts.exact
#print axioms AspisR1.PoolL_LengthFacts.wrong
#print axioms AspisR1.PoolL_LengthOccupied.disjoint
#print axioms AspisR1.PoolL_LengthOccupied.rejects
#print axioms AspisR1.PoolL_MarkerAccepted.accepted
#print axioms AspisR1.PoolL_MarkerControl.control
#print axioms AspisR1.PoolL_MarkerLengthFacts.exact
#print axioms AspisR1.PoolL_MarkerLengthReject.occupied
#print axioms AspisR1.PoolL_MarkerReach.reachable
#print axioms AspisR1.PoolL_MarkerRoleControl.control
#print axioms AspisR1.PoolL_MarkerRoleEffects.occupied_frame
#print axioms AspisR1.PoolL_MarkerRoleReject.occupied
#print axioms AspisR1.PoolL_PayerAccepted.accepted
#print axioms AspisR1.PoolL_PayerControl.control
#print axioms AspisR1.PoolL_PayerReach.reachable
#print axioms AspisR1.PoolL_Physical.key_eq
#print axioms AspisR1.PoolL_Physical.actual_length
#print axioms AspisR1.PoolL_Physical.not_empty
#print axioms AspisR1.PoolL_PhysicalAlias.length_alias
#print axioms AspisR1.PoolL_PhysicalAlias.empty_alias
#print axioms AspisR1.PoolL_PhysicalAlias.observe_alias
#print axioms AspisR1.PoolL_PhysicalAllocate.excluded
#print axioms AspisR1.PoolL_PhysicalCanonical.excluded
#print axioms AspisR1.PoolL_PhysicalClose.excluded
#print axioms AspisR1.PoolL_PhysicalFresh.excluded
#print axioms AspisR1.PoolL_PhysicalMarker.excluded
#print axioms AspisR1.PoolL_PhysicalPlan.excluded
#print axioms AspisR1.PoolL_ProgramAccepted.accepted
#print axioms AspisR1.PoolL_ProgramControl.control
#print axioms AspisR1.PoolL_RoleComposition.blocked
#print axioms AspisR1.PoolL_RoleComposition.rejected_result
#print axioms AspisR1.PoolL_RoleReach.canonical
#print axioms AspisR1.PoolL_RoleReach.fresh
#print axioms AspisR1.PoolL_RoleReach.marker
#print axioms AspisR1.PoolL_VaultAccepted.accepted
#print axioms AspisR1.PoolL_VaultControl.control
#print axioms AspisR1.PoolL_VaultReach.reachable
#print axioms AspisR1.PoolL_VerifierScopes.V2_observation
#print axioms AspisR1.PoolL_VerifierScopes.V1_prefix
