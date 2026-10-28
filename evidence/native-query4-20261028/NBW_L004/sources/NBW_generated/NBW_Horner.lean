import NBO_Audit
set_option autoImplicit false
noncomputable section
namespace NBW_Horner
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open NBO_TailDomain (WideCanonical)
abbrev Mul := Stage2E → Stage2E → Result Stage2E
/-- Local wide multiplication domain law. Exact native arithmetic binding
is NBC_FieldOps, not discharged by this domain induction. -/
def Total (mul : Mul) : Prop := ∀ x y, WideCanonical x → WideCanonical y →
 ∃ out, mul x y=ok out ∧ WideCanonical out
/-- Coefficients in source order. Native h0+h1*a+h2*a²+h3*a³ is three
steps over h0,h1,h2, starting at the SAME h3. -/
def eval (mul : Mul) (alpha : Stage2E) : List Stage2E → Stage2E → Result Stage2E
 | [], tail => ok tail
 | h::hs, tail => do
   let prior ← eval mul alpha hs tail
   let product ← mul alpha prior
   NBO_FieldSemantics.add h product
/-- Every reached multiplication domain follows from its earlier return.
There is no independent witness for a successful fold or selected product. -/
theorem total (mul : Mul) (law : Total mul) (alpha tail : Stage2E)
 (ha : WideCanonical alpha) (ht : WideCanonical tail)
 (coefficients : List Stage2E) (hc : ∀ h ∈ coefficients, WideCanonical h) :
 ∃ out, eval mul alpha coefficients tail=ok out ∧ WideCanonical out := by
 induction coefficients with
 | nil => exact ⟨tail,rfl,ht⟩
 | cons h hs ih =>
   obtain ⟨prior,hprior,cprior⟩ := ih (by intro h mem;exact hc h (List.mem_cons_of_mem _ mem))
   obtain ⟨product,hproduct,cproduct⟩ := law alpha prior ha cprior
   obtain ⟨out,hout,cout⟩ := NBO_FieldSemantics.add_total h product
     (hc h (List.mem_cons_self)) cproduct
   exact ⟨out,by simp only [eval,hprior,hproduct,bind_tc_ok,hout],cout⟩
/-- Pointwise primitive binding transports the complete Horner Result on
its proved domains. This is a mathematical child-composition lemma only. -/
theorem transport (left right : Mul) (law : Total left)
 (bind : ∀ x y, WideCanonical x → WideCanonical y → left x y=right x y)
 (alpha tail : Stage2E) (ha : WideCanonical alpha) (ht : WideCanonical tail)
 (coefficients : List Stage2E) (hc : ∀ h ∈ coefficients, WideCanonical h) :
 eval left alpha coefficients tail=eval right alpha coefficients tail := by
 induction coefficients with
 | nil => rfl
 | cons h hs ih =>
   have hhs : ∀ h ∈ hs, WideCanonical h := by
     intro h mem;exact hc h (List.mem_cons_of_mem _ mem)
   obtain ⟨prior,hprior,cprior⟩ := total left law alpha tail ha ht hs hhs
   have same := ih hhs
   simp only [eval,←same,hprior,bind_tc_ok,bind alpha prior ha cprior]
#print axioms total
#print axioms transport
end NBW_Horner
end
