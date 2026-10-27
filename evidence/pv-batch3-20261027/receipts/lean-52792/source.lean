import PV_B3_CanonicalPrepare
import PV_B3_CanonicalPreparedComponent
import PV_B3_CanonicalCAdd
import PV_B3_CanonicalCSub
import PV_B3_CanonicalMulR
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
 theorem prepared_mul (left : Prepared) (right : aspis_core.field.QM31) (hr : Q right) :
    ∃ z, PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.mul left right = .ok z ∧ Q z := by
  obtain ⟨a,ha⟩ := index_total left.components 0#usize (by decide)
  obtain ⟨b,hb⟩ := index_total left.components 1#usize (by decide)
  obtain ⟨c,hc⟩ := index_total left.components 2#usize (by decide)
  obtain ⟨m0,hm0,hcm0⟩ := prepared_component a right.c0 hr.1
  obtain ⟨m1,hm1,hcm1⟩ := prepared_component b right.c1 hr.2
  obtain ⟨s,hs,hcs⟩ := current_cadd right.c0 right.c1 hr.1 hr.2
  obtain ⟨m2,hm2,hcm2⟩ := prepared_component c s hcs
  obtain ⟨r,hrr,hcr⟩ := current_mulr m1 hcm1
  obtain ⟨d,hd,hcd⟩ := current_cadd m0 r hcm0 hcr
  obtain ⟨e,he,hce⟩ := current_csub m2 m0 hcm2 hcm0
  obtain ⟨f,hf,hcf⟩ := current_csub e m1 hce hcm1
  refine ⟨⟨d,f⟩,?_,hcd,hcf⟩
  simp only [PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier.mul,
    ha,hb,hc,hm0,hm1,hs,hm2,hrr,hd,he,hf,bind_tc_ok]
#print axioms prepared_mul
end PV_B3_Canonical
