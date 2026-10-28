import PV_L2C_NativeFold
import Mathlib.Data.Fintype.Fin
set_option autoImplicit false
namespace PV_L2C_NativeQ
open PV_L2C_M31
/-- The four native QM31 limbs in c0.a,c0.b,c1.a,c1.b order. Addition and
subtraction in CM31 and QM31 call precisely these four M31 operations. -/
abbrev Q := Fin 4 → word
def Canonical (q : Q) := ∀ i, canonical (q i)
def zero : Q := fun _ => 0
def addQ (x y : Q) : Q := fun i => add (x i) (y i)
def subQ (x y : Q) : Q := fun i => sub (x i) (y i)
def decodeQ (x : Q) : Fin 4 → ZMod p := fun i => decode (x i)

theorem zero_canonical : Canonical zero := by intro i; unfold zero canonical p; decide
#print axioms zero_canonical

theorem add_canonical (x y : Q) (hx : Canonical x) (hy : Canonical y) : Canonical (addQ x y) :=
  fun i => PV_L2C_M31.add_canonical (x i) (y i) (hx i) (hy i)
#print axioms add_canonical

theorem sub_canonical (x y : Q) (hx : Canonical x) (hy : Canonical y) : Canonical (subQ x y) :=
  fun i => PV_L2C_M31.sub_canonical (x i) (y i) (hx i) (hy i)
#print axioms sub_canonical

theorem add_decode (x y : Q) (hx : Canonical x) (hy : Canonical y) :
    decodeQ (addQ x y)=decodeQ x+decodeQ y := by
  funext i
  exact PV_L2C_M31.add_decode (x i) (y i) (hx i) (hy i)
#print axioms add_decode

theorem sub_decode (x y : Q) (hx : Canonical x) (hy : Canonical y) :
    decodeQ (subQ x y)=decodeQ x-decodeQ y := by
  funext i
  exact PV_L2C_M31.sub_decode (x i) (y i) (hx i) (hy i)
#print axioms sub_decode

theorem decode_injective (x y : Q) (hx : Canonical x) (hy : Canonical y)
    (h : decodeQ x=decodeQ y) : x=y := by
  funext i
  exact PV_L2C_M31.decode_injective (x i) (y i) (hx i) (hy i) (congrFun h i)
#print axioms decode_injective

theorem zero_decode : decodeQ zero=0 := by funext i; simp [decodeQ,zero,decode]
#print axioms zero_decode

theorem zero_guard (q : Q) (hq : Canonical q) (hz : decodeQ q=0) :
    decide (q≠zero)=false := by
  have he := decode_injective q zero hq zero_canonical (hz.trans zero_decode.symm)
  simp [he]
#print axioms zero_guard
end PV_L2C_NativeQ
