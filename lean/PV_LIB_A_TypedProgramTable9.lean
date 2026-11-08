import PV_LIB_A_TypedProgramTable8
import PV_LIB_A_OptionDestruct157
set_option autoImplicit false
namespace PV_LIB_A_TypedProgramTable9
open PV_STX2_Syntax PV_LIB_A_CellSetBegin PV_LIB_A_TypedDestruct

def bind (fid : Nat) (g : Generics) : Option PV_STX2_SliceSyntax.Program :=
  if fid = 157 then PV_LIB_A_OptionDestruct157.instantiate g
  else PV_LIB_A_TypedProgramTable8.bind fid g

def selected (fn : Data) : Option PV_STX2_SliceSyntax.Program := do
  let token ← PV_LIB_A_GenericDropBinding.normalized fn
  let fid ← PV_THR2_OffPath.functionId token
  let ptr ← member "Regular" token
  let raw ← member "generics" ptr
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

theorem inherited (fid : Nat) (g : Generics) (other : fid ≠ 157) :
    bind fid g = PV_LIB_A_TypedProgramTable8.bind fid g := by
  simp only [bind,other,↓reduceIte]

theorem exact (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (body : PV_STX2_SliceSyntax.Program) (h : selected fn = some body) :
    programs P fn = some body := by simp only [programs,h]

theorem away (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (h : selected fn = none) : programs P fn = P fn := by simp only [programs,h]

#print axioms bind
#print axioms selected
#print axioms programs
#print axioms option
#print axioms inherited
#print axioms exact
#print axioms away
end PV_LIB_A_TypedProgramTable9
