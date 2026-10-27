import R1Z.PV_Canon_MReduce
import R1Z.PV_Canon_Mul
import R1Z.PV_Canon_Sub
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_cmul (x y : aspis_core.field.CM31) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul x y = .ok z ∧ C z := by
  obtain ⟨a,ha,hca⟩ := current_mul x.a y.a
  obtain ⟨b,hb,hcb⟩ := current_mul x.b y.b
  let v := U64.wrapping_mul
    (U64.wrapping_add (UScalar.cast .U64 x.a) (UScalar.cast .U64 x.b))
    (U64.wrapping_add (UScalar.cast .U64 y.a) (UScalar.cast .U64 y.b))
  obtain ⟨c,hc,hcc⟩ := current_mreduce v
  obtain ⟨d,hd,hcd⟩ := current_sub a b hca hcb
  obtain ⟨e,he,hce⟩ := current_sub c a hcc hca
  obtain ⟨f,hf,hcf⟩ := current_sub e b hce hcb
  refine ⟨⟨d,f⟩,?_,hcd,hcf⟩
  simp only [ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul,ha,hb,lift,bind_tc_ok]
  change (do let c ← ProverRwP7CurrentFieldSource.aspis_core.field.M31.reduce_u64 v
             let d ← S.sub a b
             let e ← S.sub c a
             let f ← S.sub e b
             ok (ProverRwFull.aspis_core.field.CM31.mk d f)) = _
  simp only [hc,hd,he,hf,bind_tc_ok]
#print axioms current_cmul
end R1Z.PV_Canon
