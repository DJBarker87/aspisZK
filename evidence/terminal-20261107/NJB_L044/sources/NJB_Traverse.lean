import NJB_StubLaws
set_option autoImplicit false
namespace AspisR1.NJB_Traverse
open Aeneas Aeneas.Std Result
/-- A size-preserving source-ordered reference traversal, used to compose
one arbitrary native lane window. It never normalizes a concrete long loop. -/
def run {α β : Type} (f : α → Result β) : (xs : List α) → Result {ys : List β // ys.length=xs.length}
 | [] => ok ⟨[],rfl⟩
 | x::xs => do
   let y ← f x
   let ys ← run f xs
   ok ⟨y::ys.val,by simp only [List.length_cons,ys.property]⟩
/-- The callee premise is a generic support interface; every row root must
supply it from a CLOSED law, never leave it as a root hypothesis. -/
theorem result {α β γ : Type} (f : α → Result β) (p : β → Prop) (decode : β → γ)
 (value : α → γ) (xs : List α)
 (child : ∀ x∈xs,∃ y,f x=ok y ∧ p y ∧ decode y=value x) :
 ∃ ys,run f xs=ok ys ∧ (∀ y∈ys.val,p y) ∧ ys.val.map decode=xs.map value := by
 induction xs with
 | nil => exact ⟨⟨[],rfl⟩,rfl,by simp, rfl⟩
 | cons x xs ih =>
   obtain ⟨y,call,hy,vy⟩ := child x (by simp)
   obtain ⟨ys,rest,hs,vs⟩ := ih (fun z hz=>child z (by simp [hz]))
   refine ⟨⟨y::ys.val,by simp only [List.length_cons,ys.property]⟩,?_,?_,?_⟩
   · simp only [run,call,rest,bind_tc_ok]
   · intro z hz
     rcases List.mem_cons.mp hz with h | h
     · simpa only [h] using hy
     · exact hs z h
   · simp only [List.map_cons,vy,vs]
/-- A fail/div head ends the trace before any later lane is entered. -/
theorem failed_head {α β : Type} (f : α → Result β) (x : α) (xs : List α) (e : Error)
 (failed : f x=fail e) : run f (x::xs)=fail e := by
 simp only [run,failed,bind_tc_fail]
theorem diverged_head {α β : Type} (f : α → Result β) (x : α) (xs : List α)
 (diverged : f x=div) : run f (x::xs)=div := by
 simp only [run,diverged,bind_tc_div]
#print axioms result
#print axioms failed_head
#print axioms diverged_head
end AspisR1.NJB_Traverse
