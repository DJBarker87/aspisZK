import XRn_Join_Funs
import AspisR1CanonicalDotFinish.Funs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSd_DotSequence
/-- Generic stateless-callback association for the selected state-threaded
map. Arbitrary Result failures and divergence retain their first-stop order. -/
theorem stateless {T U : Type} (f : T → Result U) (xs : List T) :
 AspisV8R19.TraversalRuntime.mapState (BuiltinFnMut T U).call_mut xs f =
 (do let ys ← xs.mapM f; ok (ys,f)) := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
  simp only [AspisV8R19.TraversalRuntime.mapState,List.mapM]
  change (do let (y,f') ← (do let y ← f x; ok (y,f))
             let (ys,f'') ← AspisV8R19.TraversalRuntime.mapState (BuiltinFnMut T U).call_mut xs f'
             ok (y::ys,f'')) = _
  cases h : f x with
  | fail e => rfl
  | div => rfl
  | ok y =>
   simp only [bind_tc_ok,ih]
   cases xs.mapM f <;> rfl

/-- Four symbolic cells instantiate the generic map association. No arithmetic
recurrence or generated field term is unfolded. -/
theorem four {T U : Type} (f : T → Result U) (a b c d : T) :
 core.array.Array.map (BuiltinFnMut T U) (Array.make 4#usize [a,b,c,d]) f =
 (do let a' ← f a
     let b' ← f b
     let c' ← f c
     let d' ← f d
     ok (Array.make 4#usize [a',b',c',d'])) := by
 unfold core.array.Array.map
 rw [stateless]
 simp only [List.mapM]
 cases f a <;> simp only [bind_tc_ok,bind_tc_fail,bind_tc_div]
 case ok a' =>
  cases f b <;> simp only [bind_tc_ok,bind_tc_fail,bind_tc_div]
  case ok b' =>
   cases f c <;> simp only [bind_tc_ok,bind_tc_fail,bind_tc_div]
   case ok c' => cases f d <;> rfl
#print axioms stateless
#print axioms four
end XSd_DotSequence
