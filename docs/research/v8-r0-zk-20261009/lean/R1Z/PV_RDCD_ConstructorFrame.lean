import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD_ConstructorFrame
open Aeneas Aeneas.Std Result
/-- Generic left-to-right constructor sequencing, preserving the full Result. -/
def repeated {Value World : Type} (ctor : World → Result (Value × World)) :
    Nat → World → Result (List Value × World)
  | 0, world => ok ([],world)
  | n+1, world => do
    let head ← ctor world
    let tail ← repeated ctor n head.2
    ok (head.1::tail.1,tail.2)

theorem frame {Value World : Type} (ctor : World → Result (Value × World))
    (value : Value) (h : ∀ world, ctor world = ok (value,world)) (n : Nat) (world : World) :
    repeated ctor n world = ok (List.replicate n value,world) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeated,h,ih,List.replicate_succ]
#print axioms frame
end R1Z.PV_RDCD_ConstructorFrame
