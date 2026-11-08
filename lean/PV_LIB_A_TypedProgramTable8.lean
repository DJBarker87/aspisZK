import PV_LIB_A_GenericDropBinding
import PV_LIB_A_TypedBody405
import PV_LIB_A_TypedBody222
import PV_LIB_A_LoweredBody644
import PV_LIB_A_LoweredBody454
import PV_LIB_A_UnwindMatchCorrectness
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_TypedProgramTable8
open PV_STX2_Syntax PV_LIB_A_CellSetBegin PV_LIB_A_TypedDestruct

/-- Exact additional emitted glue/projections and both cleanup-preserving
lowered wrappers. The latter require UnwindMatch.carrier, by name. -/
def bind (fid : Nat) (g : Generics) : Option PV_STX2_SliceSyntax.Program :=
  match fid with
  | 405 => PV_LIB_A_TypedBody405.instantiate g.types
  | 222 => PV_LIB_A_TypedBody222.instantiate g.types
  | 644 => PV_LIB_A_LoweredBody644.instantiate g.types
  | 454 => PV_LIB_A_LoweredBody454.instantiate g.types
  | _ => PV_LIB_A_GenericDropBinding.bind fid g

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
  | some program => some program
  | none => P fn

theorem arc_glue (payload allocator : Data) : bind 405 ⟨[],[payload,allocator],[],[]⟩ =
    some (PV_LIB_A_TypedBody405.program [payload,allocator]) := rfl

theorem inner (payload allocator : Data) : bind 222 ⟨[],[payload,allocator],[],[]⟩ =
    some (PV_LIB_A_TypedBody222.program [payload,allocator]) := rfl

theorem hooks_drop : bind 644 ⟨[],[],[],[]⟩ =
    some (PV_LIB_A_LoweredBody644.program []) := rfl

theorem run_hooks : bind 454 ⟨[],[],[],[]⟩ =
    some (PV_LIB_A_LoweredBody454.program []) := rfl

theorem exact (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (body : PV_STX2_SliceSyntax.Program) (bound : selected fn = some body) :
    programs P fn = some body := by simp only [programs,bound]

theorem away (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data)
    (unbound : selected fn = none) : programs P fn = P fn := by
  simp only [programs,unbound]

#print axioms bind
#print axioms selected
#print axioms programs
#print axioms arc_glue
#print axioms inner
#print axioms hooks_drop
#print axioms run_hooks
#print axioms exact
#print axioms away
end PV_LIB_A_TypedProgramTable8
