import XRn_Join_Funs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRx_ListMap
/-- Symbolic source map for a stateless function item, preserving its closure
and the length proof on every list. -/
theorem source {T U : Type} (f : T → Result U) (xs : List T) (ys : List U)
 (h : List.Forall₂ (fun x y => f x=ok y) xs ys) :
 _root_.core.array.mapListFnMut (BuiltinFnMut T U) xs f=
 ok (⟨ys,h.length_eq.symm⟩,f) := by
 induction h with
 | nil => rfl
 | @cons a b xs ys head tail ih =>
  rw [_root_.core.array.mapListFnMut]
  simp only [BuiltinFnMut,head,bind_tc_ok]
  change (do
   let (rest,last) ← _root_.core.array.mapListFnMut (BuiltinFnMut T U) xs f
   ok ((⟨b::rest.val,by simpa only [List.length_cons] using congrArg Nat.succ rest.property⟩ : {l : List U // l.length=(a::xs).length}),last)) = _
  rw [ih]
  rfl
#print axioms source
end XRx_ListMap
