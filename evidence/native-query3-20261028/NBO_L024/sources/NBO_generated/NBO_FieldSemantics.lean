import NBO_FieldPorts
set_option autoImplicit false
noncomputable section
namespace NBO_FieldSemantics
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open NBO_FieldPorts
open NBO_TailDomain (WideCanonical)
def add (x y : Stage2E) : Result Stage2E := do
 let a ← AspisR1SelectedMaskProbe.field.QM31.add (toQ x.c0) (toQ y.c0)
 let b ← AspisR1SelectedMaskProbe.field.QM31.add (toQ x.c1) (toQ y.c1)
 ok (fromE (a,b))
def product (x : Stage2E) (q : Q) : Result Stage2E := do
 let a ← AspisR1SelectedMaskProbe.field.QM31.mul (toQ x.c0) (toQ q)
 let b ← AspisR1SelectedMaskProbe.field.QM31.mul (toQ x.c1) (toQ q)
 ok (fromE (a,b))
def power (x y : Q) : Result Q := do
 let q ← AspisR1SelectedMaskProbe.field.QM31.mul (toQ x) (toQ y)
 ok (fromQ q)
/-- Reuse exact retained probe arithmetic; only carrier transport is new. -/
theorem add_total (x y : Stage2E) (hx : WideCanonical x) (hy : WideCanonical y) :
 ∃ out, add x y=ok out ∧ WideCanonical out := by
 obtain ⟨a,ha,ca,_⟩ := ExtractedMaskQM31Exact.current_qm_add_exact
   (toQ x.c0) (toQ y.c0) ((canonicalQ _).mp hx.1) ((canonicalQ _).mp hy.1)
 obtain ⟨b,hb,cb,_⟩ := ExtractedMaskQM31Exact.current_qm_add_exact
   (toQ x.c1) (toQ y.c1) ((canonicalQ _).mp hx.2) ((canonicalQ _).mp hy.2)
 exact ⟨fromE (a,b),by simp only [add,ha,hb,bind_tc_ok],fromE_canonical _ ⟨ca,cb⟩⟩
theorem product_total (x : Stage2E) (q : Q)
 (hx : WideCanonical x) (hq : NBF_PowerStep.Canonical q) :
 ∃ out, product x q=ok out ∧ WideCanonical out := by
 obtain ⟨a,ha,ca,_⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact
   (toQ x.c0) (toQ q) ((canonicalQ _).mp hx.1) ((canonicalQ _).mp hq)
 obtain ⟨b,hb,cb,_⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact
   (toQ x.c1) (toQ q) ((canonicalQ _).mp hx.2) ((canonicalQ _).mp hq)
 exact ⟨fromE (a,b),by simp only [product,ha,hb,bind_tc_ok],fromE_canonical _ ⟨ca,cb⟩⟩
theorem power_total (x y : Q) (hx : NBF_PowerStep.Canonical x)
 (hy : NBF_PowerStep.Canonical y) :
 ∃ out, power x y=ok out ∧ NBF_PowerStep.Canonical out := by
 obtain ⟨q,hq,cq,_⟩ := ExtractedMaskQM31Exact.current_qm_mul_exact
   (toQ x) (toQ y) ((canonicalQ _).mp hx) ((canonicalQ _).mp hy)
 exact ⟨fromQ q,by simp only [power,hq,bind_tc_ok],fromQ_canonical _ cq⟩
/-- Exact remaining NBC source-to-probe statements. Each is ONE field
operation on its canonical argument domain, never an accumulator/query result. -/
structure NBC_Bindings (ops : Ops) : Prop where
 sum : ∀ x y, WideCanonical x → WideCanonical y → ops.op2 x y=add x y
 product : ∀ x q, WideCanonical x → NBF_PowerStep.Canonical q → ops.op3 x q=product x q
 power : ∀ x y, NBF_PowerStep.Canonical x → NBF_PowerStep.Canonical y → ops.op9 x y=power x y
/-- Domain-only tail premises follow from exact lower operation bindings. -/
theorem fields (ops : Ops) (bindings : NBC_Bindings ops) : NBO_TailDomain.NBC_Fields ops := by
 constructor
 · intro x q out hx hq run
   rw [bindings.product x q hx hq] at run
   obtain ⟨expected,hexpected,canonical⟩ := product_total x q hx hq
   have same := Result.ok.inj (hexpected.symm.trans run)
   simpa only [same] using canonical
 · intro x y out hx hy run
   rw [bindings.sum x y hx hy] at run
   obtain ⟨expected,hexpected,canonical⟩ := add_total x y hx hy
   have same := Result.ok.inj (hexpected.symm.trans run)
   simpa only [same] using canonical
 · intro x y out hx hy run
   rw [bindings.power x y hx hy] at run
   obtain ⟨expected,hexpected,canonical⟩ := power_total x y hx hy
   have same := Result.ok.inj (hexpected.symm.trans run)
   simpa only [same] using canonical
#print axioms add_total
#print axioms product_total
#print axioms power_total
#print axioms fields
end NBO_FieldSemantics
end
