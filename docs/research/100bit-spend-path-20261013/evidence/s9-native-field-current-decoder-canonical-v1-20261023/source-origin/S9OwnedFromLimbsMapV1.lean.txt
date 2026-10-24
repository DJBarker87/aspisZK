import AspisR1S9FieldOwnedV1.Funs
import AspisR1RecordParser.Funs

open Aeneas Aeneas.Std Result

namespace AspisR1S9OwnedFromLimbsMapV1

abbrev C := AspisR1S9FieldOwnedV1.field.wide_exact.WideExact
abbrev P := AspisR1RecordParser.field.wide_exact.WideExact

def cmToParser (x : AspisR1S9FieldOwnedV1.field.CM31) :
    AspisR1RecordParser.field.CM31 := ⟨x.a, x.b⟩

def qmToParser (x : AspisR1S9FieldOwnedV1.field.QM31) :
    AspisR1RecordParser.field.QM31 := ⟨cmToParser x.c0, cmToParser x.c1⟩

def wideToParser (x : C) : P := ⟨qmToParser x.c0, qmToParser x.c1⟩

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

/-- The exact `from_limbs` bodies commute under the explicit nominal
structure map. The eight range checks remain branchwise visible. -/
theorem from_limbs_maps (limbs : Array U32 8#usize) :
    mapOptionResult wideToParser
      (AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_limbs limbs) =
    AspisR1RecordParser.field.wide_exact.WideExact.from_limbs limbs := by
  simp [AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_limbs,
    AspisR1RecordParser.field.wide_exact.WideExact.from_limbs,
    AspisR1S9FieldOwnedV1.field.P, AspisR1RecordParser.field.P,
    mapOptionResult, mapResult_ite, wideToParser, qmToParser,
    cmToParser, Array.index_usize] <;>
    simp [mapResult, wideToParser, qmToParser, cmToParser]

#print axioms from_limbs_maps

end AspisR1S9OwnedFromLimbsMapV1
