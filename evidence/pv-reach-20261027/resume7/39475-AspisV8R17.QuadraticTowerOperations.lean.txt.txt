module
public import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.Tactic.Ring.Basic

/-! The retained explicit tower arithmetic, generalized over the base ring
to keep concrete ZMod/runtime dependencies out of this algebra leaf. These
are ring identities only; no field/nonresidue assumption is introduced. -/
@[expose] public section
namespace AspisV8R17.QuadraticTowerOperations
variable {F : Type*} [CommRing F]
abbrev C (F : Type*) [CommRing F] := QuadraticAlgebra F (-1) 0
def r : C F := ⟨2,1⟩
abbrev Q (F : Type*) [CommRing F] := QuadraticAlgebra (C F) r 0

def cmul (x y : C F) : C F :=
  ⟨x.re*y.re-x.im*y.im,(x.re+x.im)*(y.re+y.im)-x.re*y.re-x.im*y.im⟩
def cr (x : C F) : C F := ⟨x.re+x.re-x.im,x.re+(x.im+x.im)⟩

theorem cmul_eq (x y : C F) : cmul x y = x*y := by
  ext <;> simp [cmul] <;> ring

theorem cr_eq (x : C F) : cr x = r*x := by
  ext <;> simp [cr, r] <;> ring

def qmul (x y : Q F) : Q F :=
  let m0 := cmul x.re y.re
  let m1 := cmul x.im y.im
  ⟨m0+cr m1,cmul (x.re+x.im) (y.re+y.im)-m0-m1⟩
def qsquare (x : Q F) : Q F :=
  ⟨cmul x.re x.re+cr (cmul x.im x.im),cmul x.re x.im+cmul x.re x.im⟩

theorem qmul_eq (x y : Q F) : qmul x y = x*y := by
  apply QuadraticAlgebra.ext
  · simp [qmul, cmul_eq, cr_eq, mul_comm]
    ring
  · simp [qmul, cmul_eq, cr_eq]
    ring

theorem qsquare_eq (x : Q F) : qsquare x = x*x := by
  apply QuadraticAlgebra.ext
  · simp [qsquare, cmul_eq, cr_eq, mul_comm]
    ring
  · simp [qsquare, cmul_eq]
    ring

#print axioms cmul_eq
#print axioms cr_eq
#print axioms qmul_eq
#print axioms qsquare_eq
end AspisV8R17.QuadraticTowerOperations
