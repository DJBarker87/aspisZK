import AspisR1CanonicalDots.Funs
import ExtractedCurrentReducerOps
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotsField
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open ExtractedCurrentReducerOps
abbrev QM := field.QM31
abbrev E := field.wide_exact.WideExact

def Canonical (q : QM) : Prop :=
  q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647 ∧
  q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647

def WideCanonical (x : E) : Prop := Canonical x.c0 ∧ Canonical x.c1

theorem remainder_identity (x : U32) (hc : x.val<2147483647) :
    (x % field.P : Result U32)=.ok x := by
  have hP : field.P.val=2147483647 := by simp [field.P]
  obtain ⟨out,hr,hv⟩ := WP.spec_imp_exists
    (UScalar.rem_spec x (y:=field.P) (by rw [hP];decide))
  have he : out=x := UScalar.eq_of_val_eq (by
    rw [hv,hP,Nat.mod_eq_of_lt hc])
  simpa only [he] using hr

theorem canonical_identity (x : QM) (hc : Canonical x) :
    field.wide_exact.canonical_qm31 x=.ok x := by
  rcases hc with ⟨ha,hb,hc,hd⟩
  simp only [field.wide_exact.canonical_qm31,
    field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    remainder_identity x.c0.a ha,remainder_identity x.c0.b hb,
    remainder_identity x.c1.a hc,remainder_identity x.c1.b hd,bind_tc_ok]

theorem new_identity (x : E) (hc : WideCanonical x) :
    field.wide_exact.WideExact.new x.c0 x.c1=.ok x := by
  simp only [field.wide_exact.WideExact.new,
    canonical_identity x.c0 hc.1,canonical_identity x.c1 hc.2,bind_tc_ok]

#print axioms Canonical
#print axioms remainder_identity
#print axioms canonical_identity
#print axioms new_identity
end AspisR1.CuSavingsCanonicalDotsField
