import R1Z.PV_W_MemoryLift
import R1Z.PV_W_Enriched
set_option autoImplicit false
namespace R1Z.PV_W_EnrichedMemory
open PV_W_Enriched PV_W_Threading
variable {Os Fs S Extra A C : Type}

/-- A concrete commit into the enriched carrier's allocator state. Native
allocator-accessible process state must be represented in S, as in the
Physical.Runtime package; no generic allocator frame law is inferred. -/
def commit (w : World Os Fs S Extra) (s : S) : World Os Fs S Extra :=
  {w with process := {w.process with allocator := s}}

theorem commit_allocator (w : World Os Fs S Extra) (s : S) :
    (commit w s).process.allocator = s := rfl

theorem commit_os (w : World Os Fs S Extra) (s : S) : (commit w s).os = w.os := rfl

theorem commit_filesystem (w : World Os Fs S Extra) (s : S) :
    (commit w s).filesystem = w.filesystem := rfl

def effect (step : S → A × S) :
    M (World Os Fs S Extra) (Option C) Aeneas.Std.Error A :=
  PV_W_MemoryLift.statePair (fun w => w.process.allocator) commit step

theorem effect_os (step : S → A × S) (w : World Os Fs S Extra) :
    (effect (C := C) step w).world.os = w.os := rfl

theorem effect_filesystem (step : S → A × S) (w : World Os Fs S Extra) :
    (effect (C := C) step w).world.filesystem = w.filesystem := rfl

theorem effect_projected_trace (step : S → A × S) (w : World Os Fs S Extra) :
    projectTrace World.os (effect (C := C) step w).calls = [] := rfl

theorem effect_allocator (step : S → A × S) (w : World Os Fs S Extra) :
    (effect (C := C) step w).world.process.allocator = (step w.process.allocator).2 := rfl

#print axioms commit_allocator
#print axioms commit_os
#print axioms commit_filesystem
#print axioms effect_os
#print axioms effect_filesystem
#print axioms effect_projected_trace
#print axioms effect_allocator
end R1Z.PV_W_EnrichedMemory
