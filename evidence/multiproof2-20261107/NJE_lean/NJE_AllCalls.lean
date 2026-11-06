import NJE_AllAdapter

set_option autoImplicit false
noncomputable section
namespace NJE_AllCalls
open Aeneas Aeneas.Std Result ControlFlow

def body {α : Type} (f : core.ops.function.FnMut Unit α Bool) (s : List α × Unit) :
    Result (ControlFlow (List α × Unit) (Bool × List α × Unit)) := do
 let (item,tail) ← (NJE_AllAdapter.listInst α).next s.1
 match item with
 | none => ok (done (true,tail,s.2))
 | some x =>
   let (b,u) ← f.call_mut s.2 x
   if b then ok (cont (tail,u)) else ok (done (false,tail,u))

theorem loop_total {α : Type} (f : core.ops.function.FnMut Unit α Bool) (p : α → Bool) :
    ∀ xs : List α, (∀ x∈xs, f.call_mut () x=ok (p x,())) →
      ∃ tail, loop (body f) (xs,())=ok (xs.all p,tail,()) := by
 intro xs
 induction xs with
 | nil =>
   intro laws
   refine ⟨[],?_⟩
   rw [loop.eq_def]
   simp [body,NJE_AllAdapter.listInst,List.all]
 | cons x xs ih =>
   intro laws
   have head := laws x (by simp)
   obtain ⟨tail,h⟩ := ih (by intro y hy;exact laws y (List.mem_cons_of_mem _ hy))
   by_cases holds : p x=true
   · refine ⟨tail,?_⟩
     rw [loop.eq_def]
     simpa [body,NJE_AllAdapter.listInst,head,holds,List.all] using h
   · refine ⟨xs,?_⟩
     rw [loop.eq_def]
     simp [body,NJE_AllAdapter.listInst,head,holds,List.all]

theorem default_all {α : Type} (f : core.ops.function.FnMut Unit α Bool) (p : α → Bool)
    (xs : List α) (laws : ∀ x∈xs, f.call_mut () x=ok (p x,())) :
    ∃ tail, NFU_Retarget.core.iter.traits.iterator.Iterator.all.default
      (NJE_AllAdapter.listInst α) f xs ()=ok (xs.all p,tail) := by
 obtain ⟨tail,h⟩ := loop_total f p xs laws
 refine ⟨tail,?_⟩
 unfold NFU_Retarget.core.iter.traits.iterator.Iterator.all.default
 change (do let outcome ← loop (body f) (xs,());ok (outcome.1,outcome.2.1))=ok (xs.all p,tail)
 rw [h]
 rfl

#print loop_total
#print axioms loop_total
#print default_all
#print axioms default_all
end NJE_AllCalls
end
