import R1Z.PV_CB_Op109RefFuns
set_option autoImplicit false
namespace R1Z.PV_RDCD_CanonicalSource
open Aeneas Aeneas.Std Result
abbrev Q := PV_CB_ShippedOp109Ref.aspis_core.field.QM31
/-- The anonymous deployed closure has no captures, hence one environment value. -/
structure Environment where

def environment : Environment := ⟨⟩
def dropEnvironment {World : Type} (_ : Environment) (world : World) : Result World := ok world

def applyReduce (_ : Environment) (x : U32) : Result U32 := do
  PV_CB_ShippedOp109Ref.aspis_core.field.ct.reduce64 (UScalar.cast .U64 x)
/-- Exact CT branch: the four calls occur in c0.a,c0.b,c1.a,c1.b order. -/
def source (value : Q) : Result Q := do
  let reduce := applyReduce environment
  let a ← reduce value.c0.a
  let b ← reduce value.c0.b
  let c ← reduce value.c1.a
  let d ← reduce value.c1.b
  ok ⟨⟨a,b⟩,⟨c,d⟩⟩

theorem environment_unique (env : Environment) : env = environment := by cases env; rfl

theorem drop_frame {World : Type} (env : Environment) (world : World) :
    dropEnvironment env world = ok world := rfl
/-- Beta reduction only: no arithmetic implementation is replaced or assumed. -/
theorem reference (value : Q) :
    source value = PV_CB_ShippedOp109Ref.owned_wide_new.canonical_qm31 value := rfl

#print axioms environment_unique
#print axioms drop_frame
#print axioms reference
end R1Z.PV_RDCD_CanonicalSource
