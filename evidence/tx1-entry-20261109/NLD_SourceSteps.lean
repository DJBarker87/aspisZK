import NLD_FoldLaw
set_option autoImplicit false
namespace AspisR1.NLD
open Aeneas Aeneas.Std Result
/-- Pure source-action erasure. Native actions use their actual post-states
and cannot invoke this lemma without a separate frame certificate. -/
theorem step_result {A B : Type} (site : Site) (reply : Result B)
    (k : B → Program A) (s : ParentState) :
    (run (.step site (fun pre => (reply,pre)) (fun b _ => k b)) s).1 =
      (do let b ← reply; (run (k b) s).1) := by
  cases reply <;> rfl

def returned {A : Type} (site : Site) (reply : Result A) : Program A :=
  .step site (fun pre => (reply,pre)) fun a _ => .done a

theorem returned_result {A : Type} (site : Site) (reply : Result A) (s : ParentState) :
    (run (returned site reply) s).1 = reply := by cases reply <;> rfl

#print axioms step_result
#print axioms returned_result
end AspisR1.NLD
