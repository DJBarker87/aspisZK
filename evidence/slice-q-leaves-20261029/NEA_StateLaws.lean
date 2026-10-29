import NEA_FoldStateRef.Funs
import NEA_FoldModel
set_option autoImplicit false
noncomputable section
namespace NEA_StateLaws
open Aeneas Aeneas.Std Result
open NEA_FoldModel

def lift {A : Type} (r : Result A) : Result (A × Unit) := do
  let x ← r
  ok (x,())
theorem step {A B : Type} (r : Result A) (k : A → Unit → Result B) :
    (do let (x,s) ← lift r; k x s) = (do let x ← r; k x ()) := by
  cases r <;> rfl
theorem lift_bind {A B : Type} (r : Result A) (k : A → Result B) :
    lift (do let x ← r; k x) = (do let x ← r; lift (k x)) := by
  cases r <;> rfl

def ops : NEA_FoldStateRef.NEA_Ops Unit W U32 where
  add := fun _ x y => lift (NEA_FoldModel.ops.add x y)
  sub := fun _ x y => lift (NEA_FoldModel.ops.sub x y)
  mul := fun _ x y => lift (NEA_FoldModel.ops.mul x y)
  scale := fun _ x y => lift (NEA_FoldModel.ops.scale x y)
  base_mul := fun _ x y => lift (NEA_FoldModel.ops.base_mul x y)
#print axioms step
#print axioms lift_bind
end NEA_StateLaws
end
