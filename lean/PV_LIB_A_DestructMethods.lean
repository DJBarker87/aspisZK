import PV_LIB_A_TypedDestruct
set_option autoImplicit false
namespace PV_LIB_A_DestructMethods
open PV_STX2_Syntax PV_LIB_A_CellSetBegin PV_LIB_A_TypedDestruct
/- Exact Destruct::drop_glue method0 mappings from retained thread LLBC. -/
def implementation : Nat → Option (Nat × Nat × Nat)
  | 8 => some (120, 2, 0)
  | 9 => some (131, 0, 0)
  | 10 => some (133, 2, 0)
  | 13 => some (156, 2, 0)
  | 14 => some (157, 1, 0)
  | 15 => some (158, 2, 0)
  | 16 => some (163, 2, 0)
  | 25 => some (215, 0, 0)
  | 28 => some (221, 0, 2)
  | 30 => some (228, 0, 0)
  | 40 => some (273, 1, 1)
  | 54 => some (326, 2, 0)
  | 59 => some (343, 1, 0)
  | 62 => some (357, 0, 0)
  | 64 => some (373, 0, 0)
  | 73 => some (386, 0, 0)
  | 76 => some (405, 2, 0)
  | 80 => some (409, 1, 0)
  | 90 => some (434, 2, 1)
  | 97 => some (461, 1, 1)
  | 110 => some (509, 1, 0)
  | 118 => some (534, 0, 0)
  | 121 => some (554, 0, 0)
  | 137 => some (589, 2, 0)
  | 144 => some (608, 0, 0)
  | 150 => some (624, 0, 0)
  | 161 => some (645, 1, 0)
  | 163 => some (655, 0, 0)
  | 165 => some (657, 0, 0)
  | 166 => some (659, 0, 0)
  | 167 => some (660, 0, 0)
  | 168 => some (661, 2, 0)
  | 171 => some (666, 0, 0)
  | 172 => some (667, 0, 1)
  | 179 => some (685, 0, 0)
  | 184 => some (691, 0, 0)
  | 201 => some (756, 0, 0)
  | _ => none
def adtImpl : Data → Option Nat
  | .object [("Adt", (.number 8))] => some 8
  | .object [("Adt", (.number 10))] => some 9
  | .object [("Adt", (.number 16))] => some 13
  | .object [("Adt", (.number 17))] => some 14
  | .object [("Adt", (.number 12))] => some 16
  | .object [("Adt", (.number 58))] => some 25
  | .object [("Adt", (.number 15))] => some 28
  | .object [("Adt", (.number 1))] => some 30
  | .object [("Adt", (.number 66))] => some 40
  | .object [("Adt", (.number 7))] => some 54
  | .object [("Adt", (.number 92))] => some 62
  | .object [("Adt", (.number 69))] => some 64
  | .object [("Adt", (.number 101))] => some 73
  | .object [("Adt", (.number 78))] => some 80
  | .object [("Adt", (.number 109))] => some 90
  | .object [("Adt", (.number 93))] => some 97
  | .object [("Adt", (.number 18))] => some 110
  | .object [("Adt", (.number 130))] => some 118
  | .object [("Adt", (.number 94))] => some 121
  | .atom "Tuple" => some 137
  | .object [("Adt", (.number 142))] => some 144
  | .object [("Adt", (.number 111))] => some 150
  | .object [("Adt", (.number 131))] => some 161
  | .object [("Adt", (.number 163))] => some 163
  | .object [("Adt", (.number 140))] => some 165
  | .object [("Adt", (.number 135))] => some 166
  | .object [("Adt", (.number 136))] => some 167
  | .object [("Adt", (.number 164))] => some 168
  | .object [("Adt", (.number 146))] => some 171
  | .object [("Adt", (.number 147))] => some 172
  | .object [("Adt", (.number 158))] => some 179
  | .object [("Adt", (.number 169))] => some 184
  | .object [("Adt", (.number 173))] => some 201
  | _ => none

def concrete (id : Nat) (g : Generics) : Option Resolution := do
  let (fid,types,regions) ← implementation id
  if g.types.length = types ∧ g.regions.length = regions ∧
      g.constants = [] ∧ g.traits = [] then
    pure (.call (fnPtr fid {g with regions := g.regions ++ [.atom "Erased"]}))
  else none

/-- UntrackedDestruct dispatch uses the actual normalized type. Constrained
impls, unknown types, slices and dynamic vtables remain explicitly unbound. -/
def byType (ty : Data) : Option Resolution := do
  match ty with
  | .object [("Literal",_)] => pure .noop
  | .object [("Ref",_)] => pure .noop
  | .object [("RawPtr",_)] => pure .noop
  | .object [("Adt",a)] =>
    let id ← member "id" a
    let raw ← member "generics" a
    let g ← generics raw
    let i ← adtImpl id
    concrete i g
  | _ => none

/-- One named resolver for the exact emitted Destruct witness. No-op requires
NoopDestruct itself; UntrackedDestruct does not imply no-op. -/
def resolve (ty witness : Data) : Option Resolution := do
  let kind ← member "kind" witness
  match member "TraitImpl" kind with
  | some impl =>
    let .number id ← member "id" impl | none
    let raw ← member "generics" impl
    let g ← generics raw
    concrete id g
  | none =>
    let builtin ← member "BuiltinOrAuto" kind
    match member "builtin_data" builtin with
    | some (.atom "NoopDestruct") => pure .noop
    | some (.atom "UntrackedDestruct") => byType ty
    | _ => none

theorem concrete_shape (id : Nat) (g : Generics) (fid types regions : Nat)
    (method : implementation id = some (fid,types,regions))
    (typeArity : g.types.length = types) (regionArity : g.regions.length = regions)
    (constants : g.constants = []) (traits : g.traits = []) :
    concrete id g = some (.call (fnPtr fid {g with regions := g.regions ++ [.atom "Erased"]})) := by
  unfold concrete
  rw [method]
  change (if g.types.length = types ∧ g.regions.length = regions ∧
    g.constants = [] ∧ g.traits = [] then _ else _) = _
  rw [if_pos ⟨typeArity,regionArity,constants,traits⟩]
  rfl

#print axioms implementation
#print axioms adtImpl
#print axioms concrete
#print axioms byType
#print axioms resolve
#print axioms concrete_shape
end PV_LIB_A_DestructMethods
