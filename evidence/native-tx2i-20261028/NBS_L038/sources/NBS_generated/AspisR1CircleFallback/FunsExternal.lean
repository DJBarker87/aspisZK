-- Focused external-function adapter for the frozen fallback-only extraction.
-- The opaque callee is implemented by the already-proved R72 circle mapper.
import Aeneas
import AspisR1CircleFallback.Types
import AspisR72Sampler.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1CircleFallback

def toR72CM (x : field.CM31) : AspisR72Sampler.field.CM31 := ⟨x.a, x.b⟩

def toR72QM (x : field.QM31) : AspisR72Sampler.field.QM31 :=
  ⟨toR72CM x.c0, toR72CM x.c1⟩

def fromR72CM (x : AspisR72Sampler.field.CM31) : field.CM31 := ⟨x.a, x.b⟩

def fromR72QM (x : AspisR72Sampler.field.QM31) : field.QM31 :=
  ⟨fromR72CM x.c0, fromR72CM x.c1⟩

def fromR72Point (x : AspisR72Sampler.circle.SecureCirclePoint) :
    circle.SecureCirclePoint := ⟨fromR72QM x.x, fromR72QM x.y⟩

def fromR72Error : AspisR72Sampler.circle.CirclePointError → circle.CirclePointError
  | .SingularParameter => .SingularParameter
  | .ParameterInCm31Subfield => .ParameterInCm31Subfield

/-- The opaque source callee is instantiated by the retained R72 mapper;
the representation maps are the explicit nested-record field projections. -/
def circle.secure_ood_circle_point_from_parameter (q : field.QM31) :
    Result (core.result.Result circle.SecureCirclePoint circle.CirclePointError) := do
  let r ← AspisR72Sampler.circle.secure_ood_circle_point_from_parameter (toR72QM q)
  match r with
  | .Ok p => ok (.Ok (fromR72Point p))
  | .Err e => ok (.Err (fromR72Error e))

end AspisR1CircleFallback
