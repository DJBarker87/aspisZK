import PV_LIB_A_DropMetadata
set_option autoImplicit false
namespace PV_LIB_A_TypedDestruct
open PV_STX2_Syntax
open PV_LIB_A_CellSetBegin

/-- Resolve hash-cons metadata without guessing the meaning of unknown keys.
The finite fuel is a parser bound; exhaustion is an explicit missing binding. -/
def normalize : Nat → Data → Option Data
  | 0, _ => none
  | n+1, .object [("Deduplicated",.number key)] => do
      let value ← PV_LIB_A_DropMetadata.lookup key
      normalize n value
  | n+1, .object [("HashConsedValue",.array [_,value])] => normalize n value
  | n+1, .object fields => do
      let fields ← fields.mapM (fun (k,v) => do pure (k,← normalize n v))
      pure (.object fields)
  | n+1, .array values => do pure (.array (← values.mapM (normalize n)))
  | _+1, value => some value

/-- Substitute the actual T list into normalized emitted metadata. Body-local
regions and the actual destructor witness are retained, not erased. -/
def substitute : Nat → List Data → Data → Option Data
  | 0, _, _ => none
  | _+1, types, .object [("TypeVar",.object [("Free",.number i)])] => types[i]?
  | n+1, types, .object fields => do
      let fields ← fields.mapM (fun (k,v) => do pure (k,← substitute n types v))
      pure (.object fields)
  | n+1, types, .array values => do pure (.array (← values.mapM (substitute n types)))
  | _+1, _, value => some value

structure Generics where
  regions : List Data
  types : List Data
  constants : List Data
  traits : List Data
  deriving Repr

def generics (raw : Data) : Option Generics := do
  let .array regions ← member "regions" raw | none
  let .array types ← member "types" raw | none
  let .array constants ← member "const_generics" raw | none
  let .array traits ← member "trait_refs" raw | none
  pure ⟨regions,types,constants,traits⟩

def encode (g : Generics) : Data := .object
  [("regions",.array g.regions),("types",.array g.types),
   ("const_generics",.array g.constants),("trait_refs",.array g.traits)]

def fnPtr (fid : Nat) (g : Generics) : Data := .object
  [("kind",.object [("Fun",.object [("Regular",.number fid)])]),("generics",encode g)]

/-- A concrete selected glue token or a documented no-op. Absence means an
unbound destructor, never successful identity destruction. -/
inductive Resolution where
  | noop
  | call (fn : Data)
  deriving Repr

/-- Named metadata equality, independent of any handler's answer. -/
theorem substitute_type (n i : Nat) (types : List Data) :
    substitute (n+1) types (.object [("TypeVar",.object [("Free",.number i)])]) = types[i]? := rfl

theorem preserves_atom (n : Nat) (types : List Data) (s : String) :
    substitute (n+1) types (.atom s) = some (.atom s) := rfl

theorem generics_roundtrip (g : Generics) : generics (encode g) = some g := by
  cases g
  rfl

#print axioms normalize
#print axioms substitute
#print axioms generics
#print axioms encode
#print axioms fnPtr
#print axioms substitute_type
#print axioms preserves_atom
#print axioms generics_roundtrip
end PV_LIB_A_TypedDestruct
