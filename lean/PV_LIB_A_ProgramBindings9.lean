import PV_LIB_A_TypedProgramTable9
import PV_LIB_A_AllocatorProvenance
set_option autoImplicit false
namespace PV_LIB_A_ProgramBindings9
open PV_STX2_Syntax PV_LIB_A_TypedDestruct

/-- Global is the source's empty ZST. Its own glue228 has no fields or custom
Drop to execute. This is a documented pure destructor, not an erased A rule. -/
def PV_THR2_LibrarySemantics_GlobalDestruct228 : PV_STX2_SliceSyntax.Program :=
  ⟨228,.atom "documented empty Global destruction",.null,
   [.leaf (.aggregateMove ⟨228,0,.atom "Global unit"⟩ (.local 0)
      PV_LIB_A_GenericDropMachine.unitTag []),
    .leaf (.ret ⟨228,1,.atom "Global return"⟩ (.local 0))]⟩

def bind (fid : Nat) (g : Generics) : Option PV_STX2_SliceSyntax.Program :=
  match fid with
  | 218 => PV_LIB_A_TypedBody218.instantiate g.types
  | 315 => PV_LIB_A_TypedBody315.instantiate g.types
  | 228 => if g.types = [] ∧ g.constants = [] ∧ g.traits = [] then
      some PV_THR2_LibrarySemantics_GlobalDestruct228 else none
  | _ => PV_LIB_A_TypedProgramTable9.bind fid g

def selected (fn : Data) : Option PV_STX2_SliceSyntax.Program := do
  let token ← PV_LIB_A_GenericDropBinding.normalized fn
  let fid ← PV_THR2_OffPath.functionId token
  let ptr ← PV_LIB_A_CellSetBegin.member "Regular" token
  let raw ← PV_LIB_A_CellSetBegin.member "generics" ptr
  let g ← generics raw
  bind fid g

def programs (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data) :
    Option PV_STX2_SliceSyntax.Program :=
  match selected fn with
  | some body => some body
  | none => P fn

theorem option (ty : Data) (regions : List Data) :
    bind 157 ⟨regions,[ty],[],[]⟩ =
      some (PV_LIB_A_OptionDestruct157.PV_THR2_LibrarySemantics_OptionDestruct157 ty) := rfl

theorem allocator_constructor (payload allocator : Data) :
    bind 315 ⟨[],[payload,allocator],[],[]⟩ =
      some (PV_LIB_A_TypedBody315.program [payload,allocator]) := rfl

theorem global_only (regions : List Data) : bind 228 ⟨regions,[],[],[]⟩ =
    some PV_THR2_LibrarySemantics_GlobalDestruct228 := rfl

theorem exact (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (body : PV_STX2_SliceSyntax.Program) (h : selected fn = some body) :
    programs P fn = some body := by simp only [programs,h]

#print axioms PV_THR2_LibrarySemantics_GlobalDestruct228
#print axioms bind
#print axioms selected
#print axioms programs
#print axioms option
#print axioms allocator_constructor
#print axioms global_only
#print axioms exact
end PV_LIB_A_ProgramBindings9
