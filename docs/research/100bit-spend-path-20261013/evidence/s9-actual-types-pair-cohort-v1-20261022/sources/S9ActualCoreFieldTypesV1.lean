import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace AspisR1S9ActualFieldTypesCutV1

@[reducible]
def field.M31 := Std.U32

structure field.CM31 where
  a : field.M31
  b : field.M31

structure field.QM31 where
  c0 : field.CM31
  c1 : field.CM31

structure field.wide_exact.WideExact where
  c0 : field.QM31
  c1 : field.QM31

inductive transport.Variant where
| S1 : transport.Variant
| S2 : transport.Variant
| D : transport.Variant

def transport.Variant.read_discriminant (x : transport.Variant) : Isize :=
  match x with
  | .S1 => 0#isize
  | .S2 => 1#isize
  | .D => 2#isize

@[simp] theorem transport.Variant.read_discriminant_S1 :
    transport.Variant.read_discriminant .S1 = 0#isize := rfl
@[simp] theorem transport.Variant.read_discriminant_S2 :
    transport.Variant.read_discriminant .S2 = 1#isize := rfl
@[simp] theorem transport.Variant.read_discriminant_D :
    transport.Variant.read_discriminant .D = 2#isize := rfl

instance _root_.AspisR1S9ActualFieldTypesCutV1.transport.Variant.instDiscriminant :
    Aeneas.Std.Discriminant transport.Variant Isize where
  read_discriminant := transport.Variant.read_discriminant

structure weights.Weights where
  variant : transport.Variant
  factors : Array (Array (Array field.QM31 4#usize) 5#usize) 5#usize
  points : Array (Array field.QM31 10#usize) 3#usize
  extra : Array field.QM31 2#usize

def weights.Weights.scalar_factor.closure :=
  Array field.wide_exact.WideExact 4#usize × Array field.QM31 4#usize

end AspisR1S9ActualFieldTypesCutV1
