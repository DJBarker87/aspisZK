import SAQ_GeometrySource
set_option autoImplicit false
noncomputable section
namespace NBS_FibreIndex
open Aeneas Aeneas.Std Result AspisR1
/-- The exact frozen checked constructor, retaining the caller's error carrier.
The native total constructor is checked by NBS_K001. -/
def checked {Err : Type} (indexError : Err) (index : Usize) :
    Result (core.result.Result Usize Err) :=
  if index.val<262144 then ok (.Ok index) else ok (.Err indexError)

theorem accepted {Err : Type} (indexError : Err) (index out : Usize)
    (run : checked indexError index=ok (.Ok out)) : out=index ∧ out.val<262144 := by
  unfold checked at run
  split at run
  · cases run;exact ⟨rfl,by assumption⟩
  · cases run

def install {Err : Type} (indexError : Err) (ops : Port3_NativeGeometryBody.Ops Err) :
    Port3_NativeGeometryBody.Ops Err :=
  { SAQ_GeometrySource.install ops with op12 := checked indexError }

/-- Constructor domain is proved for the SAME returned checked index. No
successful constructor output is selected independently of its input. -/
theorem remaining {Err : Type} (indexError : Err) (ops : Port3_NativeGeometryBody.Ops Err) :
    SAQ_GeometrySource.Remaining (install indexError ops) := by
  constructor
  intro index out run
  exact accepted indexError index out run

#print axioms accepted
#print axioms remaining
end NBS_FibreIndex
