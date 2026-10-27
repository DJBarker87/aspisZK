import R1Z.PV_Canon_MReduce
import R1Z.PV_Canon_Mul
import R1Z.PV_Canon_Double
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_csquare (x : aspis_core.field.CM31) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.CM31.square x = .ok z ∧ C z := by
  let p := ProverRwP7CurrentFieldSource.aspis_core.field.P
  let v := U64.wrapping_mul
    (U64.wrapping_add (UScalar.cast .U64 x.a) (UScalar.cast .U64 x.b))
    (U64.wrapping_sub (U64.wrapping_add (UScalar.cast .U64 x.a) (UScalar.cast .U64 p)) (UScalar.cast .U64 x.b))
  obtain ⟨a,ha,hca⟩ := current_mreduce v
  obtain ⟨b,hb,hcb⟩ := current_mul x.a x.b
  obtain ⟨c,hc,hcc⟩ := current_double b hcb
  refine ⟨⟨a,c⟩,?_,hca,hcc⟩
  simp only [ProverRwP7CurrentFieldSource.aspis_core.field.CM31.square,lift,bind_tc_ok]
  change (do let a ← ProverRwP7CurrentFieldSource.aspis_core.field.M31.reduce_u64 v
             let b ← S.mul x.a x.b
             let c ← ProverRwP7CurrentFieldSource.aspis_core.field.M31.double b
             ok (ProverRwFull.aspis_core.field.CM31.mk a c)) = _
  simp only [ha,hb,hc,bind_tc_ok]
#print axioms current_csquare
end R1Z.PV_Canon
