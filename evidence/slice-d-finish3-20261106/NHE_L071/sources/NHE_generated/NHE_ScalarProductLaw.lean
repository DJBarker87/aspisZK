import NHE_ScalePort
set_option autoImplicit false
namespace NHE_ScalarProductLaw
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem word (x : U32) (small : x.val<2147483647) : x%2147483647#u32=ok x := by
 have positive : (2147483647#u32).val≠0 := by decide
 obtain ⟨z,run,value⟩ := WP.spec_imp_exists (UScalar.rem_spec (x:=x) (y:=2147483647#u32) positive)
 have same : z=x := UScalar.eq_of_val_eq (by rw [value];change x.val%2147483647=x.val;exact Nat.mod_eq_of_lt small)
 simpa only [same] using run

theorem canonical (x : NQ) (hx : canonQ x) :
 FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok x := by
 simp only [FIo_Native.aspis_core.field.wide_exact.canonical_qm31,FIo_Native.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,FIo_Native.aspis_core.field.P,word _ hx.1.1,word _ hx.1.2,word _ hx.2.1,word _ hx.2.2,bind_tc_ok]

theorem product (x : NE) (q : NQ) (hx : canonE x) (hq : canonQ q) :
 ∃ out,FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x q=ok out ∧ canonE out ∧
 ew out=(mulQ (qw x.c0) (qw q),mulQ (qw x.c1) (qw q)) := by
 obtain ⟨a,ha,ca,va⟩ := LPi_TowerValues.qm_mul x.c0 q hx.1 hq
 obtain ⟨b,hb,cb,vb⟩ := LPi_TowerValues.qm_mul x.c1 q hx.2 hq
 exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31,canonical q hq,ha,hb,bind_tc_ok],⟨ca,cb⟩,Prod.ext va vb⟩

#print axioms word
#print axioms canonical
#print axioms product
end NHE_ScalarProductLaw
