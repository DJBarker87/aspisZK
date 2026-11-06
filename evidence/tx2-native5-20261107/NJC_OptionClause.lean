import NJC_ReaderEmission
import NJC_ClosedCalls
set_option autoImplicit false
noncomputable section
namespace NJC_OptionClause
open Aeneas Aeneas.Std Result AspisR1

/-- The literal extracted standard helper retains the entire value, not a
selected coordinate. Native E Option controls cover all eight limbs. -/
theorem source {A Err : Type} (value : Option A) (err : Err) :
 NJC_ReaderEmission.core.option.Option.ok_or value err=
 ok (match value with | none => core.result.Result.Err err | some x => .Ok x) := by
 cases value <;> rfl

theorem frame {A Err S Event : Type} (value : Option A) (err : Err) (state : S) :
 NEB_PureFrame.run (Event:=Event) state
 (NJC_ReaderEmission.core.option.Option.ok_or value err)=
 ok ((match value with | none => core.result.Result.Err err | some x => .Ok x),state,[]) := by
 rw [source]
 rfl

#print axioms source
#print axioms frame
end NJC_OptionClause
