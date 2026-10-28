import NBS_FibreIndex
import Port5Q1_GeometryAccessor
set_option autoImplicit false
noncomputable section
namespace NBS_GeometryInstall
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev Ops := Port3_NativeGeometryBody.Ops

def primitives {Err : Type} (indexError : Err) (seed : Ops Err) : Ops Err :=
  SAQ_GeometrySource.install {seed with op12 := NBS_FibreIndex.checked indexError}

theorem domain {Err : Type} (indexError : Err) (seed : Ops Err) :
    Port5Q1_Domain.SessionADomain (primitives indexError seed) := by
  apply SAQ_GeometrySource.domain
  constructor
  intro index out run
  exact NBS_FibreIndex.accepted indexError index out run

theorem canonical {Err : Type} (indexError : Err) (seed : Ops Err) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (primitives indexError seed) :=
  SAQ_GeometrySource.canonical _

def installed {Err : Type} (indexError : Err) (seed : Ops Err) : Ops Err :=
  Port5Q1_GeometryTerminal.install (primitives indexError seed)

/-- The actual selected geometry's interpretation on the SAME successful
model call. No independently chosen flat vector, inverse or line state. Native
whole-body association is a separate P6 obligation. -/
theorem accepted {Err : Type} (indexError : Err) (seed : Ops Err)
    (queries : Array U32 22#usize) (start stop : Usize) (out : verifier.QueryGeometry)
    (nonempty : start.val<stop.val)
    (run : Port3_GeometryStage.geometry (installed indexError seed) queries start stop=ok (.Ok out)) :
    Port5Q1_GeometryBinding.Binding queries start stop out := by
  apply Port5Q1_GeometryReads.accepted (primitives indexError seed)
    (canonical indexError seed) (domain indexError seed)
  · exact SAQ_GeometrySource.multiply _
  · exact SAQ_GeometrySource.one _
  · exact SAQ_GeometrySource.inverse _
  · exact nonempty
  · exact run

#print axioms domain
#print axioms canonical
#print axioms accepted
end NBS_GeometryInstall
