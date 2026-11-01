import PV_EVH_PublishCompact
set_option autoImplicit false
namespace PV_EVH_ViewBoundary
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
/-- A finished runtime failure cannot erase to a source call modeled as a
pure successful value. This does not refute native execution: its full outcome
model must retain runtime faults and delimit the source-view domain explicitly. -/
theorem failure_excludes_value {A : Type} (m : P A) (value : A)
    (w : World) (error : Error)
    (failed : (m w).status = .finished (.fail error)) :
    ¬FinishedView m (.ok value) := by
  intro view
  have impossible := view w (.fail error) failed
  cases impossible

variable [ExternalTypes] [ExternalFuns]
/-- In particular, closing this global compatibility structure by silently
excluding the allocator's abort path would not establish native coverage. -/
theorem capacity_failure_excludes_compatible (c : PV_EVH_PublishCompact.Callees)
    (T : Type) (capacity : Usize) (w : World) (error : Error)
    (failed : (c.withCapacity_OPEN T capacity w).status = .finished (.fail error)) :
    ¬PV_EVH_PublishCompact.Compatible c := by
  intro compatible
  exact failure_excludes_value (c.withCapacity_OPEN T capacity)
    (alloc.vec.Vec.with_capacity T capacity) w error failed
    (compatible.withCapacity_fixed T capacity)
#print axioms failure_excludes_value
#print axioms capacity_failure_excludes_compatible
end PV_EVH_ViewBoundary
