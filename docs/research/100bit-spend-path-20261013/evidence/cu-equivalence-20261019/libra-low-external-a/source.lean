import AspisR1LibraLow.Types
import AspisR1WideArithmetic.Funs
import CuSavingsArrayBuilder
set_option autoImplicit false
namespace AspisR1LibraLow
open Aeneas Aeneas.Std Result
abbrev W := AspisR1WideArithmetic.field.wide_exact.WideExact
abbrev K := AspisR1WideArithmetic.field.QM31
def toK (q : field.QM31) : K := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromK (q : K) : field.QM31 := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toE (e : field.wide_exact.WideExact) : W := ⟨toK e.c0,toK e.c1⟩
def fromE (e : W) : field.wide_exact.WideExact := ⟨fromK e.c0,fromK e.c1⟩
@[simp] theorem to_fromE (e : W) : toE (fromE e)=e := rfl
@[simp] theorem from_toE (e : field.wide_exact.WideExact) : fromE (toE e)=e := rfl
def field.wide_exact.WideExact.mul (x y : field.wide_exact.WideExact) : Result field.wide_exact.WideExact := do
 let z ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul (toE x) (toE y)
 .ok (fromE z)
def field.wide_exact.WideExact.mul_m31 (x : field.wide_exact.WideExact) (q : field.M31) : Result field.wide_exact.WideExact := do
 let z ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul_m31 (toE x) q
 .ok (fromE z)
abbrev field.M31.mul := AspisR1WideArithmetic.field.M31.mul
abbrev core.array.from_fn := @AspisR1.CuSavingsArrayBuilder.build
#print axioms to_fromE
#print axioms from_toE
end AspisR1LibraLow
