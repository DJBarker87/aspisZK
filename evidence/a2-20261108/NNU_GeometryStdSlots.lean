import NNU_GeometrySelected
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_GeometryStdSlots
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody NNU_GeometryInstall

theorem map_error {C : Type} (g : Ops C) : @(terminal g).op2 = @Port4C_GeometryStd.mapError := rfl

theorem slots {C C' : Type} (g : Ops C) (h : Ops C') :
 @(terminal g).op1 = @(terminal h).op1 ∧
 @(terminal g).op3 = @(terminal h).op3 ∧
 @(terminal g).op4 = @(terminal h).op4 ∧
 (terminal g).op6 = (terminal h).op6 ∧
 @(terminal g).mapIterator = @(terminal h).mapIterator := by
 exact ⟨rfl,rfl,rfl,rfl,rfl⟩
#print axioms map_error
#print axioms slots
end AspisR1.NNU_GeometryStdSlots
end
