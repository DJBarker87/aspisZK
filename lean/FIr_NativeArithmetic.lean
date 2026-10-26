import FIq_Native02
import FIo_FieldBridge
import ExtractedMaskQM31Exact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_NativeArithmetic
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (map map_bind map_ok)
abbrev NQ := FIq_Native.field.QM31
abbrev NC := FIq_Native.field.CM31
abbrev PQ := AspisR1SelectedMaskProbe.field.QM31
abbrev PC := AspisR1SelectedMaskProbe.field.CM31

def cm (x : NC) : PC := ⟨x.a,x.b⟩
def qm (x : NQ) : PQ := ⟨cm x.c0,cm x.c1⟩

theorem bind_map {A B C : Type} (f : A → B) (m : Result A) (k : B → Result C) :
    (do let x←map f m;k x)=(do let x←m;k (f x)) := by
  cases m <;> rfl

theorem m31_add (x y : U32) : FIq_Native.field.M31.add x y=
    AspisR1SelectedMaskProbe.field.M31.add x y := by
  simp only [FIq_Native.field.M31.add,AspisR1SelectedMaskProbe.field.M31.add,
    FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]

theorem m31_sub (x y : U32) : FIq_Native.field.M31.sub x y=
    AspisR1SelectedMaskProbe.field.M31.sub x y := by
  simp only [FIq_Native.field.M31.sub,AspisR1SelectedMaskProbe.field.M31.sub,
    FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]

theorem m31_reduce (x : U64) : FIq_Native.field.M31.reduce_u64 x=
    AspisR1SelectedMaskProbe.field.M31.reduce_u64 x := by
  simp only [FIq_Native.field.M31.reduce_u64,AspisR1SelectedMaskProbe.field.M31.reduce_u64,
    FIq_Native.field.reduce_u64,AspisR1SelectedMaskProbe.field.reduce_u64,
    FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]

theorem m31_mul (x y : U32) : FIq_Native.field.M31.mul x y=
    AspisR1SelectedMaskProbe.field.M31.mul x y := by
  simp only [FIq_Native.field.M31.mul,AspisR1SelectedMaskProbe.field.M31.mul,
    FIq_Native.field.reduce_u64,AspisR1SelectedMaskProbe.field.reduce_u64,
    FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]

#print axioms bind_map
#print axioms m31_add
#print axioms m31_sub
#print axioms m31_reduce
#print axioms m31_mul
end AspisR1.FIr_NativeArithmetic
end
