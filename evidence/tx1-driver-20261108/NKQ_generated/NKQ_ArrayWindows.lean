import NKA_FinishStages
set_option autoImplicit false
namespace AspisR1.NKQ_ArrayWindows
open Aeneas Aeneas.Std Result

def cell {α : Type} {n : Usize} (a : Array α n) (i : Nat) (h : i<n.val) : α :=
 a.val[i]'(by have len:=a.property;omega)

theorem extensional {α : Type} {n : Usize} (a b : Array α n)
 (point : ∀ i (h : i<n.val),cell a i h=cell b i h) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem
 · have ha:=a.property;have hb:=b.property;omega
 · intro i ha hb
   exact point i (by have len:=a.property;omega)

theorem read {α : Type} {n : Usize} (a : Array α n) (i : Usize) (h : i.val<n.val) :
 Array.index_usize a i=ok (cell a i.val h) := by
 simp [Array.index_usize,cell,h]

/-- Prefix induction for a state-preserving from_fn closure on its actual
bounded index list. The old unrestricted pure law is insufficient outside
that list; this version adds no caller success or endpoint premise. -/
theorem fromFnLoop_bounded {T C : Type} (f : core.ops.function.FnMut C Usize T)
 (g : Usize → T) (c : C) (is : List Usize)
 (step : ∀ i∈is,f.call_mut c i=ok (g i,c)) :
 OraclePortStdBuilder.fromFnLoop f is c=ok (is.map g,c) := by
 induction is with
 | nil => rfl
 | cons head tail ih =>
   have first:=step head (List.mem_cons_self ..)
   have rest : ∀ i∈tail,f.call_mut c i=ok (g i,c) := fun i member=>step i (List.mem_cons_of_mem head member)
   simp only [OraclePortStdBuilder.fromFnLoop,first,bind_tc_ok,ih rest,List.map_cons]
#print axioms extensional
#print axioms read
#print axioms fromFnLoop_bounded
end AspisR1.NKQ_ArrayWindows
