import AspisR1S9WideMulM31CutV1.Funs
import CurrentWideBaseBridge
import CurrentWideMulM31V13
import R22CurrentReducerMul
import S9WideMulM31ActualM31MapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9WideMulM31FullResultMapV1

/-- Identity on the common U32 scalar carrier; explicit record maps below
transport the independently generated source-cut structures. -/
def mapM31 (x : AspisR1S9WideMulM31CutV1.field.M31) :
    AspisR1CurrentWide.field.M31 := x

def mapCM (x : AspisR1S9WideMulM31CutV1.field.CM31) :
    AspisR1CurrentWide.field.CM31 := ⟨mapM31 x.a, mapM31 x.b⟩

def mapQM (x : AspisR1S9WideMulM31CutV1.field.QM31) :
    AspisR1CurrentWide.field.QM31 := ⟨mapCM x.c0, mapCM x.c1⟩

def mapWide (x : AspisR1S9WideMulM31CutV1.field.wide_exact.WideExact) :
    AspisR1CurrentWide.field.wide_exact.WideExact := ⟨mapQM x.c0, mapQM x.c1⟩

def mapR {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapR_id {A : Type} (r : Result A) : mapR id r = r := by
  cases r <;> rfl

theorem mapR_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) :
    mapR f (Bind.bind r k) = Bind.bind r (fun x => mapR f (k x)) := by
  cases r <;> rfl

theorem m31_mul_eq_current (x y : AspisR1S9WideMulM31CutV1.field.M31) :
    AspisR1S9WideMulM31CutV1.field.M31.mul x y =
      AspisR1CurrentWide.field.M31.mul x y := by
  calc
    AspisR1S9WideMulM31CutV1.field.M31.mul x y =
        .ok (AspisR1.R22CurrentReducerMul.wrappingMul x y) :=
      AspisR1S9WideMulM31ActualM31MapV1.actual_m31_mul_eq_R22_wrappingMul x y
    _ = AspisR1Qm31ArithmeticProbe.field.M31.mul x y :=
      (AspisR1.R22CurrentReducerMul.current_mul_agrees x y).symm
    _ = AspisR1CurrentWide.field.M31.mul x y := by
      simpa only [AspisR1CurrentWide.Proof.m31_mul_same]

theorem m31_mul_result_map (x y : AspisR1S9WideMulM31CutV1.field.M31) :
    mapR mapM31 (AspisR1S9WideMulM31CutV1.field.M31.mul x y) =
      AspisR1CurrentWide.field.M31.mul (mapM31 x) (mapM31 y) := by
  change mapR id (AspisR1S9WideMulM31CutV1.field.M31.mul x y) =
    AspisR1CurrentWide.field.M31.mul x y
  rw [mapR_id]
  exact m31_mul_eq_current x y

theorem cm_mul_m31_result_map
    (x : AspisR1S9WideMulM31CutV1.field.CM31)
    (s : AspisR1S9WideMulM31CutV1.field.M31) :
    mapR mapCM (AspisR1S9WideMulM31CutV1.field.CM31.mul_m31 x s) =
      AspisR1CurrentWide.field.CM31.mul_m31 (mapCM x) (mapM31 s) := by
  simp only [AspisR1S9WideMulM31CutV1.field.CM31.mul_m31,
    AspisR1CurrentWide.field.CM31.mul_m31, mapR_bind, mapM31, mapCM,
    m31_mul_eq_current, bind_tc_ok] <;> rfl


#print axioms m31_mul_eq_current
#print axioms m31_mul_result_map
#print axioms cm_mul_m31_result_map

end AspisR1S9WideMulM31FullResultMapV1
