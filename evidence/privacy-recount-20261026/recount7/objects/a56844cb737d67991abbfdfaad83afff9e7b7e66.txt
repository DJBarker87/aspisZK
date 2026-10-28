import PV_B3_CanonicalMReduce
import PV_B3_CanonicalMul
import PV_B3_CanonicalDouble
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
 theorem current_csquare (x : aspis_core.field.CM31) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.CM31.square x = .ok z ∧ C z := by
  let p := PV_B3_Copy_117.aspis_core.field.P
  let v := U64.wrapping_mul
    (U64.wrapping_add (UScalar.cast .U64 x.a) (UScalar.cast .U64 x.b))
    (U64.wrapping_sub (U64.wrapping_add (UScalar.cast .U64 x.a) (UScalar.cast .U64 p)) (UScalar.cast .U64 x.b))
  obtain ⟨a,ha,hca⟩ := current_mreduce v
  obtain ⟨b,hb,hcb⟩ := current_mul x.a x.b
  obtain ⟨c,hc,hcc⟩ := current_double b hcb
  refine ⟨⟨a,c⟩,?_,hca,hcc⟩
  simp only [PV_B3_Copy_117.aspis_core.field.CM31.square,lift,bind_tc_ok]
  change (do let a ← PV_B3_Copy_117.aspis_core.field.M31.reduce_u64 v
             let b ← S.mul x.a x.b
             let c ← PV_B3_Copy_117.aspis_core.field.M31.double b
             ok (PV_B3_Copy_117.aspis_core.field.CM31.mk a c)) = _
  simp only [ha,hb,hc,bind_tc_ok]
#print axioms current_csquare
end PV_B3_Canonical
