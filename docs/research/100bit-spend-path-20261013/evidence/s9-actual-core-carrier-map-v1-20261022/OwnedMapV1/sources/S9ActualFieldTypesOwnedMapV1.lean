import S9ActualCoreFieldTypesV1
import AspisR1S9FieldOwnedV1.Types

set_option autoImplicit false

namespace AspisR1S9ActualFieldTypesOwnedMapV1

abbrev ActualM31 := AspisR1S9ActualFieldTypesCutV1.field.M31
abbrev ActualCM31 := AspisR1S9ActualFieldTypesCutV1.field.CM31
abbrev ActualQM31 := AspisR1S9ActualFieldTypesCutV1.field.QM31
abbrev ActualWide := AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact

abbrev OwnedM31 := AspisR1S9FieldOwnedV1.field.M31
abbrev OwnedCM31 := AspisR1S9FieldOwnedV1.field.CM31
abbrev OwnedQM31 := AspisR1S9FieldOwnedV1.field.QM31
abbrev OwnedWide := AspisR1S9FieldOwnedV1.field.wide_exact.WideExact

def toFieldOwnedM31 (x : ActualM31) : OwnedM31 := x

def toFieldOwnedCM31 (x : ActualCM31) : OwnedCM31 := ⟨x.a, x.b⟩

def toFieldOwnedQM31 (x : ActualQM31) : OwnedQM31 :=
  ⟨toFieldOwnedCM31 x.c0, toFieldOwnedCM31 x.c1⟩

def toFieldOwned (x : ActualWide) : OwnedWide :=
  ⟨toFieldOwnedQM31 x.c0, toFieldOwnedQM31 x.c1⟩

theorem toFieldOwnedM31_injective : Function.Injective toFieldOwnedM31 := by
  intro x y h
  exact h

theorem toFieldOwnedCM31_injective : Function.Injective toFieldOwnedCM31 := by
  intro x y h
  have ha : x.a = y.a := congrArg (fun z : OwnedCM31 => z.a) h
  have hb : x.b = y.b := congrArg (fun z : OwnedCM31 => z.b) h
  cases x with
  | mk xa xb => cases y with
    | mk ya yb => cases ha; cases hb; rfl

theorem toFieldOwnedQM31_injective : Function.Injective toFieldOwnedQM31 := by
  intro x y h
  have hc0 : x.c0 = y.c0 :=
    toFieldOwnedCM31_injective (congrArg (fun z : OwnedQM31 => z.c0) h)
  have hc1 : x.c1 = y.c1 :=
    toFieldOwnedCM31_injective (congrArg (fun z : OwnedQM31 => z.c1) h)
  cases x with
  | mk xa xb => cases y with
    | mk ya yb => cases hc0; cases hc1; rfl

theorem toFieldOwned_injective : Function.Injective toFieldOwned := by
  intro x y h
  have hc0 : x.c0 = y.c0 :=
    toFieldOwnedQM31_injective (congrArg (fun z : OwnedWide => z.c0) h)
  have hc1 : x.c1 = y.c1 :=
    toFieldOwnedQM31_injective (congrArg (fun z : OwnedWide => z.c1) h)
  cases x with
  | mk xa xb => cases y with
    | mk ya yb => cases hc0; cases hc1; rfl

theorem toFieldOwnedM31_roundtrip (x : ActualM31) :
    toFieldOwnedM31 x = x := rfl

theorem toFieldOwnedCM31_roundtrip (x : ActualCM31) :
    toFieldOwnedCM31 x = ⟨x.a, x.b⟩ := rfl

theorem toFieldOwnedQM31_roundtrip (x : ActualQM31) :
    toFieldOwnedQM31 x = ⟨toFieldOwnedCM31 x.c0, toFieldOwnedCM31 x.c1⟩ := rfl

theorem toFieldOwned_roundtrip (x : ActualWide) :
    toFieldOwned x = ⟨toFieldOwnedQM31 x.c0, toFieldOwnedQM31 x.c1⟩ := rfl


#print axioms toFieldOwnedM31_injective
#print axioms toFieldOwnedCM31_injective
#print axioms toFieldOwnedQM31_injective
#print axioms toFieldOwned_injective
#print axioms toFieldOwnedM31_roundtrip
#print axioms toFieldOwnedCM31_roundtrip
#print axioms toFieldOwnedQM31_roundtrip
#print axioms toFieldOwned_roundtrip

end AspisR1S9ActualFieldTypesOwnedMapV1
