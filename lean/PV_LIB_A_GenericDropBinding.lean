import PV_LIB_A_ExactDestructMethods
import PV_LIB_A_TypedBody486
import PV_LIB_A_TypedBody584
import PV_LIB_A_TypedBody608
import PV_LIB_A_TypedBody661
import PV_LIB_A_TypedDropSource
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_GenericDropBinding
open PV_STX2_Syntax PV_LIB_A_CellSetBegin PV_LIB_A_TypedDestruct

/-- Normalize both raw Drop FnPtrs and ordinary call tokens. -/
def normalized (fn : Data) : Option Data :=
  normalize 64 (PV_LIB_A_TypedDropSource.callToken fn)

/-- Resolve trait-method Drop0 through its actual self type and witness. Other
trait methods are not classified as destructors by their numeric index. -/
def resolveToken (fn : Data) : Option Resolution := do
  let token ← normalized fn
  let ptr ← member "Regular" token
  let kind ← member "kind" ptr
  match member "Fun" kind with
  | some _ => pure (.call ptr)
  | none =>
    let .array [witness,.number 0] ← member "Trait" kind | none
    let trait ← member "trait_decl_ref" witness
    let binder ← member "skip_binder" trait
    let .number 5 ← member "id" binder | none
    let raw ← member "generics" binder
    let g ← generics raw
    match g.types with
    | [ty] => PV_LIB_A_ExactDestructMethods.resolve ty witness
    | _ => none

/-- Exact emitted templates; type substitution also reaches every cleanup
Drop and nested generic call. No arbitrary body is supplied by a consumer. -/
def bind (fid : Nat) (g : Generics) : Option PV_STX2_SliceSyntax.Program :=
  match fid with
  | 486 => PV_LIB_A_TypedBody486.instantiate g.types
  | 584 => PV_LIB_A_TypedBody584.instantiate g.types
  | 608 => PV_LIB_A_TypedBody608.instantiate g.types
  | 661 => PV_LIB_A_TypedBody661.instantiate g.types
  | _ => none

def selected (fn : Data) : Option PV_STX2_SliceSyntax.Program := do
  let token ← normalized fn
  let fid ← PV_THR2_OffPath.functionId token
  let ptr ← member "Regular" token
  let raw ← member "generics" ptr
  let g ← generics raw
  bind fid g

/-- Override only a successfully instantiated exact template. Every other
resolver clause stays present. This is not full native-wrapper adequacy. -/
def programs (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data) :
    Option PV_STX2_SliceSyntax.Program :=
  match selected fn with
  | some program => some program
  | none => P fn

theorem arc (g : Generics) : bind 486 g = PV_LIB_A_TypedBody486.instantiate g.types := rfl
theorem slow (g : Generics) : bind 584 g = PV_LIB_A_TypedBody584.instantiate g.types := rfl
theorem weakGuard (g : Generics) : bind 661 g = PV_LIB_A_TypedBody661.instantiate g.types := rfl
theorem hooks (g : Generics) : bind 608 g = PV_LIB_A_TypedBody608.instantiate g.types := rfl

theorem exact (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (body : PV_STX2_SliceSyntax.Program) (bound : selected fn = some body) :
    programs P fn = some body := by simp only [programs,bound]

theorem away (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (unbound : selected fn = none) : programs P fn = P fn := by
  simp only [programs,unbound]

#print axioms normalized
#print axioms resolveToken
#print axioms bind
#print axioms selected
#print axioms programs
#print axioms arc
#print axioms slow
#print axioms weakGuard
#print axioms hooks
#print axioms exact
#print axioms away
end PV_LIB_A_GenericDropBinding
