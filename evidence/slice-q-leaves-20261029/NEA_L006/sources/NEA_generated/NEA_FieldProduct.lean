import NDH_Geometry
import LPi_FieldValues
set_option autoImplicit false
namespace NEA_FieldProduct
open Aeneas Aeneas.Std Result AspisR1.LPi_FieldValues
abbrev GC := AspisR1QueryGeometryActual.field.CM31
def toNative (x : GC) : NC := ⟨x.a,x.b⟩
def ofNative (x : NC) : GC := ⟨x.a,x.b⟩
def Canonical (x : GC) : Prop := x.a.val < 2147483647 ∧ x.b.val < 2147483647

def ops : AspisR1QueryGeometryActual.CM31Ops :=
  ⟨fun a b => ok ⟨a,b⟩, fun x y => do
    let z ← FIo_Native.aspis_core.field.CM31.mul (toNative x) (toNative y)
    ok (ofNative z)⟩

theorem emitted_cm (x y : GC) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul (toNative x) (toNative y)=ok z ∧
      canonC z ∧ cw z=mulC (cw (toNative x)) (cw (toNative y)) := by
  exact AspisR1.LPi_FieldValues.cm_mul (toNative x) (toNative y) hx hy

theorem geometric_cm (x y : GC) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, ops.mul x y=ok z ∧ Canonical z ∧
      (z.a.val,z.b.val)=mulC (x.a.val,x.b.val) (y.a.val,y.b.val) := by
  obtain ⟨z,run,canonical,value⟩ := emitted_cm x y hx hy
  refine ⟨ofNative z,?_,canonical,value⟩
  simp only [ops,run,bind_tc_ok]

#print axioms emitted_cm
#print axioms geometric_cm
end NEA_FieldProduct
