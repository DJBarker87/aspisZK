import AspisR1S9ActualWideMulCutV1.Funs
import AspisR1S9ActualQMMulCutV1.Funs
import S9WideSourcePrimitiveBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideSourceRecordMapV1

abbrev WideCM := AspisR1S9ActualWideMulCutV1.field.CM31
abbrev WideQM := AspisR1S9ActualWideMulCutV1.field.QM31
abbrev QCM := AspisR1S9ActualQMMulCutV1.field.CM31
abbrev QQM := AspisR1S9ActualQMMulCutV1.field.QM31
def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

def toQCM (x : WideCM) : QCM := ⟨x.a, x.b⟩
def toQQM (x : WideQM) : QQM := ⟨toQCM x.c0, toQCM x.c1⟩

private theorem mapResult_ok {A B : Type} (f : A → B) (x : A) :
    mapResult f (.ok x) = .ok (f x) := rfl

private theorem mapResult_bind {A B C : Type} (f : A → B)
    (m : Result C) (k : C → Result A) :
    mapResult f (do let x ← m; k x) = (do let x ← m; mapResult f (k x)) := by
  cases m <;> rfl

/-- The actual Wide cut's complete `mul_by_r` Result body maps to the actual
QM multiplication cut's same source body, preserving fail/div branches. -/
theorem wide_mul_by_r_maps_to_qcut (x : WideCM) :
    mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.mul_by_r x) = AspisR1S9ActualQMMulCutV1.field.mul_by_r (toQCM x) := by
  simp only [AspisR1S9ActualWideMulCutV1.field.mul_by_r, AspisR1S9ActualQMMulCutV1.field.mul_by_r, mapResult_bind,
    AspisR1S9WideSourcePrimitiveBridgeV1.wide_m31_double_eq_qcut,
    AspisR1S9WideSourcePrimitiveBridgeV1.wide_m31_sub_eq_qcut,
    AspisR1S9WideSourcePrimitiveBridgeV1.wide_m31_add_eq_qcut,
    toQCM, mapResult_ok]

/-- The QM cut has no `mul_u` declaration. This definition is the exact mapped
formula exposed by the transparent Wide source body. -/
def qcutMulUFormula (x : QQM) : Result QQM := do
  let c ← AspisR1S9ActualQMMulCutV1.field.mul_by_r x.c1
  ok { c0 := c, c1 := x.c0 }

private theorem mapResult_bind_map {A B C D : Type} (f : A → B) (g : C → D)
    (m : Result C) (k : C → Result A) (l : D → Result B)
    (h : ∀ x, mapResult f (k x) = l (g x)) :
    mapResult f (do let x ← m; k x) = (do let y ← mapResult g m; l y) := by
  cases m with
  | ok x => exact h x
  | fail e => rfl
  | div => rfl

/-- The transparent Wide `mul_u` body maps, with its complete Result behavior,
to the corresponding operation formula built from the actual QM-cut `mul_by_r`.
This does not claim a generated QM-cut `mul_u` exists. -/
theorem wide_mul_u_maps_to_qcut_formula (x : WideQM) :
    mapResult toQQM (AspisR1S9ActualWideMulCutV1.field.wide_exact.mul_u x) = qcutMulUFormula (toQQM x) := by
  calc
    mapResult toQQM (AspisR1S9ActualWideMulCutV1.field.wide_exact.mul_u x) =
        (do let c ← mapResult toQCM (AspisR1S9ActualWideMulCutV1.field.mul_by_r x.c1)
            ok { c0 := c, c1 := toQCM x.c0 }) := by
      unfold AspisR1S9ActualWideMulCutV1.field.wide_exact.mul_u
      exact mapResult_bind_map toQQM toQCM
        (AspisR1S9ActualWideMulCutV1.field.mul_by_r x.c1)
        (fun c => ok { c0 := c, c1 := x.c0 })
        (fun c => ok { c0 := c, c1 := toQCM x.c0 })
        (by intro c; simp only [mapResult, toQQM, toQCM])
    _ = qcutMulUFormula (toQQM x) := by
      unfold qcutMulUFormula
      rw [wide_mul_by_r_maps_to_qcut]
      simp only [toQQM]

#print axioms wide_mul_by_r_maps_to_qcut
#print axioms wide_mul_u_maps_to_qcut_formula

end AspisR1S9WideSourceRecordMapV1
