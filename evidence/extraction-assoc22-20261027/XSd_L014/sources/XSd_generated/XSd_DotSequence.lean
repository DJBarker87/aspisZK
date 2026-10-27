import XRx_ListMap
import AspisR1CanonicalDotFinish.Funs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSd_DotSequence
/-- Generic projected first-stop sequence law for the actual selected map.
All callback failures and divergence keep their original order. -/
theorem sequence {T U : Type} (f : T → Result U) (xs : List T) :
 (do let (ys,_) ← _root_.core.array.mapListFnMut (BuiltinFnMut T U) xs f
     ok ys.val) = xs.mapM f := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
  rw [_root_.core.array.mapListFnMut,List.mapM_cons]
  simp only [BuiltinFnMut]
  cases h : f x with
  | fail e => rfl
  | div => rfl
  | ok y =>
   simp only [bind_tc_ok]
   rw [←ih]
   generalize ht : _root_.core.array.mapListFnMut (BuiltinFnMut T U) xs f = tail at *
   cases tail with
   | ok pair => rcases pair with ⟨ys,last⟩; simp only [ht,bind_tc_ok]; rfl
   | fail e => simp only [ht,bind_tc_fail]; rfl
   | div => simp only [ht,bind_tc_div]; rfl

/-- Four arbitrary successful callback results instantiate the existing
all-list map theorem; the driver is not hand-unrolled. -/
theorem four {T U : Type} (f : T → Result U) (a b c d : T) (w x y z : U)
 (h0 : f a=ok w) (h1 : f b=ok x) (h2 : f c=ok y) (h3 : f d=ok z) :
 core.array.Array.map (BuiltinFnMut T U) (Array.make 4#usize [a,b,c,d]) f =
 ok (Array.make 4#usize [w,x,y,z]) := by
 have h : List.Forall₂ (fun a b => f a=ok b) [a,b,c,d] [w,x,y,z] :=
  .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil)))
 have hm := XRx_ListMap.source f [a,b,c,d] [w,x,y,z] h
 unfold core.array.Array.map
 change (do let (mapped,_) ← _root_.core.array.mapListFnMut (BuiltinFnMut T U) [a,b,c,d] f
            ok (⟨mapped.val,mapped.property⟩ : Array U 4#usize)) = _
 rw [hm]
 rfl
#print axioms sequence
#print axioms four
end XSd_DotSequence
