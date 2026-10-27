import PV_B3_CanonicalCMul
import PV_B3_CanonicalCAdd
import PV_B3_CanonicalCSub
import PV_B3_CanonicalMulR
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
 theorem current_qmul (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.QM31.mul x y = .ok z ∧ Q z := by
  obtain ⟨m0,hm0,hcm0⟩ := current_cmul x.c0 y.c0
  obtain ⟨m1,hm1,hcm1⟩ := current_cmul x.c1 y.c1
  obtain ⟨a,ha,hca⟩ := current_cadd x.c0 x.c1 hx.1 hx.2
  obtain ⟨b,hb,hcb⟩ := current_cadd y.c0 y.c1 hy.1 hy.2
  obtain ⟨m2,hm2,hcm2⟩ := current_cmul a b
  obtain ⟨r,hr,hcr⟩ := current_mulr m1 hcm1
  obtain ⟨c,hc,hcc⟩ := current_cadd m0 r hcm0 hcr
  obtain ⟨d,hd,hcd⟩ := current_csub m2 m0 hcm2 hcm0
  obtain ⟨e,he,hce⟩ := current_csub d m1 hcd hcm1
  refine ⟨⟨c,e⟩,?_,hcc,hce⟩
  simp only [PV_B3_Copy_117.aspis_core.field.QM31.mul,
    hm0,hm1,ha,hb,hm2,hr,hc,hd,he,bind_tc_ok]
#print axioms current_qmul
end PV_B3_Canonical
