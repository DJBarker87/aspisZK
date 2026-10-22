import S9ActualCoreFieldTypesV1
import AspisR1S9FieldOwnedV1.Funs
import S9ActualFieldTypesOwnedMapV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9ActualFieldTypesCutV1

@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [s9_helper_actual_field_types_cut::field::wide_exact::{s9_helper_actual_field_types_cut::field::wide_exact::WideExact}::from_limbs]:
    Source: 'src/field/wide_exact.rs', lines 207:4-235:5
    Visibility: public -/
def field.wide_exact.WideExact.from_limbs
  (limbs : Array Std.U32 8#usize) :
  Result (Option field.wide_exact.WideExact)
  := do
  let i ← Array.index_usize limbs 0#usize
  if i >= field.P
  then ok none
  else
    let i1 ← Array.index_usize limbs 1#usize
    if i1 >= field.P
    then ok none
    else
      let i2 ← Array.index_usize limbs 2#usize
      if i2 >= field.P
      then ok none
      else
        let i3 ← Array.index_usize limbs 3#usize
        if i3 >= field.P
        then ok none
        else
          let i4 ← Array.index_usize limbs 4#usize
          if i4 >= field.P
          then ok none
          else
            let i5 ← Array.index_usize limbs 5#usize
            if i5 >= field.P
            then ok none
            else
              let i6 ← Array.index_usize limbs 6#usize
              if i6 >= field.P
              then ok none
              else
                let i7 ← Array.index_usize limbs 7#usize
                if i7 >= field.P
                then ok none
                else
                  ok (some
                    {
                      c0 :=
                        { c0 := { a := i, b := i1 }, c1 := { a := i2, b := i3 }
                        },
                      c1 :=
                        {
                          c0 := { a := i4, b := i5 },
                          c1 := { a := i6, b := i7 }
                        }
                    })

end AspisR1S9ActualFieldTypesCutV1

namespace AspisR1S9ActualFromLimbsOwnedMapV1

abbrev ActualWide := AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact
abbrev OwnedWide := AspisR1S9FieldOwnedV1.field.wide_exact.WideExact

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

def mapOptionResult {A B : Type} (f : A → B) :
    Result (Option A) → Result (Option B) := mapResult (Option.map f)

theorem mapResult_ite {A B : Type} (f : A → B) (p : Prop) [Decidable p]
    (x y : Result A) :
    mapResult f (if p then x else y) = if p then mapResult f x else mapResult f y := by
  by_cases hp : p <;> simp [hp]

theorem actual_from_limbs_maps_to_owned (limbs : Array Std.U32 8#usize) :
    mapOptionResult AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned
      (AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact.from_limbs limbs) =
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_limbs limbs := by
  simp [AspisR1S9ActualFieldTypesCutV1.field.wide_exact.WideExact.from_limbs,
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_limbs,
    AspisR1S9ActualFieldTypesCutV1.field.P, AspisR1S9FieldOwnedV1.field.P,
    mapOptionResult, mapResult_ite,
    AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned,
    AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwnedQM31,
    AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwnedCM31,
    Array.index_usize] <;>
    simp [mapResult,
      AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwned,
      AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwnedQM31,
      AspisR1S9ActualFieldTypesOwnedMapV1.toFieldOwnedCM31]

#print axioms actual_from_limbs_maps_to_owned

end AspisR1S9ActualFromLimbsOwnedMapV1
