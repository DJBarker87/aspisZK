import AspisR1CanonicalInputs.Types
import CuSavingsWideMul
import CuSavingsArrayBuilder
set_option autoImplicit false
namespace AspisR1CanonicalInputs
open Aeneas Aeneas.Std Result
abbrev CoreK := AspisR1WideArithmetic.field.QM31
abbrev CoreE := AspisR1WideArithmetic.field.wide_exact.WideExact

def toK (x : field.QM31) : CoreK := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromK (x : CoreK) : field.QM31 := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toE (x : field.wide_exact.WideExact) : CoreE := ⟨toK x.c0,toK x.c1⟩
def fromE (x : CoreE) : field.wide_exact.WideExact := ⟨fromK x.c0,fromK x.c1⟩
def field.wide_exact.WideExact.mul (x y : field.wide_exact.WideExact) :
    Result field.wide_exact.WideExact := do
  let z ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul (toE x) (toE y)
  .ok (fromE z)
def core.array.from_fn_mut {T F : Type} (N : Usize)
    (inst : core.ops.function.FnMut F Usize T) (state : F) : Result (Array T N × F) := do
  let (xs,finalState) ← AspisR1.CuSavingsArrayBuilder.cells inst N.val 0#usize state
  .ok (⟨xs.val,xs.property⟩,finalState)
#print axioms field.wide_exact.WideExact.mul
#print axioms core.array.from_fn_mut
end AspisR1CanonicalInputs
