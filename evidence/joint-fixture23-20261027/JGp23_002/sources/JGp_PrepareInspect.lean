import JGn_CurrentPreparation
import JGn_PrepareBuffer
import JGi_TX1Ready
import FJp_Top
set_option autoImplicit false
namespace AspisR1.JGp_PrepareInspect
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
#print Ops
#print concreteInstall
#print InstalledPreparation.install
#print RowShape_InstalledSlots.verifierOps
#print compact.LOGICAL_Y1
#print aspis_core.field.wide_exact.WideExact.ZERO
#print ConcreteConstants.withConstants
#print BorrowedClaimPrepared.install
#print Aeneas.Std.alloc.vec.Vec.deref_mut
#print axioms AspisR1.FJp_Top.deployed
end AspisR1.JGp_PrepareInspect
