import NKA_FinishStages
set_option autoImplicit false
namespace AspisR1.NKQ_GetterRepeat
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Pure Result getter duplication. Fail/div terminate at the first call;
there is no second observable event or independently selected payload. -/
theorem duplicate {A B : Type} (getter : Result A) (next : A → A → Result B) :
 (do let first ← getter;let second ← getter;next first second)=
 (do let first ← getter;next first first) := by
 cases getter <;> rfl

theorem source {A : Type} (pre : r1_wire.Prefix) (row : U8)
 (next : core.result.Result r1_wire.ValidatedRecord r1_wire.Error →
  core.result.Result r1_wire.ValidatedRecord r1_wire.Error → Result A) :
 (do let first ← r1_wire.Prefix.validated_record pre row
     let second ← r1_wire.Prefix.validated_record pre row
     next first second)=
 (do let first ← r1_wire.Prefix.validated_record pre row
     next first first) := duplicate _ _
#print axioms duplicate
#print axioms source
end AspisR1.NKQ_GetterRepeat
