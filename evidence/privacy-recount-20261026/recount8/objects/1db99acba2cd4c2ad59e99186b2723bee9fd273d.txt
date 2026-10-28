import AspisR1ProducerChecked47.Funs
import ExtractedCurrentQM31Equality
/-! Nominal transport to the retained canonical arithmetic proof. This module
uses the explicitly overflow-checked extraction; native release overflow
agreement is a distinct obligation, not silently inferred here. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPrimitive47
open Aeneas Aeneas.Std Result
namespace Old
open AspisR1Qm31ArithmeticProbe
abbrev C := field.CM31
abbrev Q := field.QM31
end Old
open AspisR1ProducerChecked47
abbrev Q := field.QM31
abbrev C := field.CM31

def fromC (x : Old.C) : C := ⟨x.a,x.b⟩
def fromQ (x : Old.Q) : Q := ⟨fromC x.c0,fromC x.c1⟩
def toC (x : C) : Old.C := ⟨x.a,x.b⟩
def toQ (x : Q) : Old.Q := ⟨toC x.c0,toC x.c1⟩

theorem from_to (x : Q) : fromQ (toQ x)=x := by cases x; rfl
theorem to_from (x : Old.Q) : toQ (fromQ x)=x := by cases x; rfl

def mapR {A B : Type} (f : A → B) : Result A → Result B
 | .ok x => .ok (f x)
 | .fail e => .fail e
 | .div => .div

theorem map_bind {A B C : Type} (f : B → C) (r : Result A) (g : A → Result B) :
    mapR f (r >>= g) = r >>= (fun a => mapR f (g a)) := by cases r <;> rfl

theorem mAdd (x y : U32) : field.M31.add x y =
    AspisR1Qm31ArithmeticProbe.field.M31.add x y := by
  unfold field.M31.add AspisR1Qm31ArithmeticProbe.field.M31.add
  rw [field.P,AspisR1Qm31ArithmeticProbe.field.P]

theorem mSub (x y : U32) : field.M31.sub x y =
    AspisR1Qm31ArithmeticProbe.field.M31.sub x y := by
  unfold field.M31.sub AspisR1Qm31ArithmeticProbe.field.M31.sub
  rw [field.P,AspisR1Qm31ArithmeticProbe.field.P]

theorem mDouble (x : U32) : field.M31.double x =
    AspisR1Qm31ArithmeticProbe.field.M31.double x := by
  unfold field.M31.double AspisR1Qm31ArithmeticProbe.field.M31.double
  exact mAdd x x

theorem reduce (x : U64) : field.reduce_u64 x =
    AspisR1Qm31ArithmeticProbe.field.reduce_u64 x := by
  unfold field.reduce_u64 AspisR1Qm31ArithmeticProbe.field.reduce_u64
  rw [field.P,AspisR1Qm31ArithmeticProbe.field.P]

theorem mReduce (x : U64) : field.M31.reduce_u64 x =
    AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x := by
  simp only [field.M31.reduce_u64,AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64,reduce]

theorem mMul (x y : U32) : field.M31.mul x y =
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y := by
  simp only [field.M31.mul,AspisR1Qm31ArithmeticProbe.field.M31.mul,reduce]

theorem addC (x y : Old.C) : field.CM31.add (fromC x) (fromC y) =
    mapR fromC (AspisR1Qm31ArithmeticProbe.field.CM31.add x y) := by
  simp only [field.CM31.add,AspisR1Qm31ArithmeticProbe.field.CM31.add,map_bind]
  simp only [fromC,mAdd,mapR]

theorem subC (x y : Old.C) : field.CM31.sub (fromC x) (fromC y) =
    mapR fromC (AspisR1Qm31ArithmeticProbe.field.CM31.sub x y) := by
  simp only [field.CM31.sub,AspisR1Qm31ArithmeticProbe.field.CM31.sub,map_bind]
  simp only [fromC,mSub,mapR]

theorem mulC (x y : Old.C) : field.CM31.mul (fromC x) (fromC y) =
    mapR fromC (AspisR1Qm31ArithmeticProbe.field.CM31.mul x y) := by
  simp only [field.CM31.mul,AspisR1Qm31ArithmeticProbe.field.CM31.mul,map_bind]
  simp only [fromC,mMul,mSub,mReduce,mapR]

theorem rC (x : Old.C) : field.mul_by_r (fromC x) =
    mapR fromC (AspisR1Qm31ArithmeticProbe.field.mul_by_r x) := by
  simp only [field.mul_by_r,AspisR1Qm31ArithmeticProbe.field.mul_by_r,map_bind]
  simp only [fromC,mDouble,mSub,mAdd,mapR]

theorem addQ (x y : Old.Q) : field.QM31.add (fromQ x) (fromQ y) =
    mapR fromQ (AspisR1Qm31ArithmeticProbe.field.QM31.add x y) := by
  simp only [field.QM31.add,AspisR1Qm31ArithmeticProbe.field.QM31.add,fromQ,addC,map_bind]
  cases AspisR1Qm31ArithmeticProbe.field.CM31.add x.c0 y.c0 <;>
    cases AspisR1Qm31ArithmeticProbe.field.CM31.add x.c1 y.c1 <;> rfl

def subOld (x y : Old.Q) : Result Old.Q := do
  let c0 ← AspisR1Qm31ArithmeticProbe.field.CM31.sub x.c0 y.c0
  let c1 ← AspisR1Qm31ArithmeticProbe.field.CM31.sub x.c1 y.c1
  ok ⟨c0,c1⟩

theorem subQ (x y : Old.Q) : field.QM31.sub (fromQ x) (fromQ y) =
    mapR fromQ (subOld x y) := by
  simp only [field.QM31.sub,subOld,fromQ,subC,map_bind]
  cases AspisR1Qm31ArithmeticProbe.field.CM31.sub x.c0 y.c0 <;>
    cases AspisR1Qm31ArithmeticProbe.field.CM31.sub x.c1 y.c1 <;> rfl

theorem bind_map {A B C : Type} (f : A → B) (r : Result A) (g : B → Result C) :
    (mapR f r >>= g) = r >>= (fun a => g (f a)) := by cases r <;> rfl

theorem mulQ (x y : Old.Q) : field.QM31.mul (fromQ x) (fromQ y) =
    mapR fromQ (AspisR1Qm31ArithmeticProbe.field.QM31.mul x y) := by
  simp only [field.QM31.mul,AspisR1Qm31ArithmeticProbe.field.QM31.mul,fromQ,
    mulC,addC,subC,rC,map_bind,bind_map]
  rfl

#print axioms bind_map
#print axioms mulQ
#print axioms mAdd
#print axioms mSub
#print axioms mDouble
#print axioms reduce
#print axioms mReduce
#print axioms mMul
#print axioms from_to
#print axioms to_from
#print axioms map_bind
#print axioms addC
#print axioms subC
#print axioms mulC
#print axioms rC
#print axioms addQ
#print axioms subQ
end R1Z.ProverCommitPrimitive47
