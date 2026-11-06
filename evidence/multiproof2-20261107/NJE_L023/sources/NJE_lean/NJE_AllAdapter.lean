import NFU_LPl_Kit_FunsExternal
import NJA_WellIteration

set_option autoImplicit false
noncomputable section
namespace NJE_AllAdapter
open Aeneas Aeneas.Std Result ControlFlow

impl_def listInst (α : Type) : core.iter.traits.iterator.Iterator (List α) α := {
 next := fun xs => match xs with
   | [] => ok (none,[])
   | x::tail => ok (some x,tail)
 enumerate := core.iter.traits.iterator.Iterator.enumerate.trait_default (listInst α)
}

def predicate {α : Type} (p : α → Bool) : core.ops.function.FnMut Unit α Bool where
 FnOnceInst := {call_once := fun _ x => ok (p x)}
 call_mut := fun _ x => ok (p x,())

def body {α : Type} (p : α → Bool) (s : List α × Unit) :
    Result (ControlFlow (List α × Unit) (Bool × List α × Unit)) := do
 let (item,tail) ← (listInst α).next s.1
 match item with
 | none => ok (done (true,tail,()))
 | some x => if p x then ok (cont (tail,())) else ok (done (false,tail,()))

theorem loop_total {α : Type} (p : α → Bool) (xs : List α) :
    ∃ tail, loop (body p) (xs,())=ok (xs.all p,tail,()) := by
 induction xs with
 | nil =>
   refine ⟨[],?_⟩
   rw [loop.eq_def]
   simp [body,listInst,List.all]
 | cons x xs ih =>
   obtain ⟨tail,h⟩ := ih
   by_cases holds : p x=true
   · refine ⟨tail,?_⟩
     rw [loop.eq_def]
     simpa [body,listInst,holds,List.all] using h
   · refine ⟨xs,?_⟩
     rw [loop.eq_def]
     simp [body,listInst,holds,List.all]

theorem default_all {α : Type} (p : α → Bool) (xs : List α) :
    ∃ tail,
      NFU_Retarget.core.iter.traits.iterator.Iterator.all.default
        (listInst α) (predicate p) xs ()=ok (xs.all p,tail) := by
 obtain ⟨tail,h⟩ := loop_total p xs
 refine ⟨tail,?_⟩
 unfold NFU_Retarget.core.iter.traits.iterator.Iterator.all.default
 change (do let out ← loop (body p) (xs,()); ok (out.1,out.2.1))=ok (xs.all p,tail)
 rw [h]
 rfl

#print loop_total
#print axioms loop_total
#print default_all
#print axioms default_all
#print Aeneas.Std.core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.all
end NJE_AllAdapter
end
