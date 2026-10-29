import R1Z.PV_OWND_ActualItems
import R1Z.PV_OWND_EndpointCounter
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialCheck
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWND_EndpointCounter
inductive CheckError where
 | shape
 | endpoint (row : UInt16)
 deriving DecidableEq
/-- Pure scalar interpretation of the checks after initialization. Native u8
stack-array initialization and accesses still require source binding. -/
def checks (b : Buffer Link) : Except CheckError Unit :=
 if b.length≠127 then .error .shape else
 match check (PV_OWND_ActualItems.items b) (fun _=>0) (fun _=>0) with
 | .error (.endpointCapacity row) => .error (.endpoint row)
 | .ok _ => .ok ()
/-- A normal Result error consumes the Vec owner before the POD/free suffix;
allocator failure/divergence preserves its actual post-world. -/
def finish {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (error : CheckError → E) (b : Buffer Link) : Action S X E (Buffer Link) :=
 match checks b with
 | .ok () => lift (.ok b)
 | .error e => bind (dropOwned b.owner (fun _=>dropVecPod dealloc b.token b.cell))
   (fun _=>lift (.fail (error e)))
attribute [local irreducible] checks finish
end R1Z.PV_OWND_InitialCheck
