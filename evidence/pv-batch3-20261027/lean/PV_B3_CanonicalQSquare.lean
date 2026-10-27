import PV_B3_CanonicalCSquare
import PV_B3_CanonicalCMul
import PV_B3_CanonicalCAdd
import PV_B3_CanonicalCDouble
import PV_B3_CanonicalMulR
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
 theorem current_qsquare (x : aspis_core.field.QM31) :
    ∃ z, PV_B3_Copy_117.aspis_core.field.QM31.square x = .ok z ∧ Q z := by
  obtain ⟨a,ha,hca⟩ := current_csquare x.c0
  obtain ⟨b,hb,hcb⟩ := current_csquare x.c1
  obtain ⟨c,hc,hcc⟩ := current_mulr b hcb
  obtain ⟨d,hd,hcd⟩ := current_cadd a c hca hcc
  obtain ⟨e,he,hce⟩ := current_cmul x.c0 x.c1
  obtain ⟨f,hf,hcf⟩ := current_cdouble e hce
  refine ⟨⟨d,f⟩,?_,hcd,hcf⟩
  simp only [PV_B3_Copy_117.aspis_core.field.QM31.square,
    ha,hb,hc,hd,he,hf,bind_tc_ok]
#print axioms current_qsquare
end PV_B3_Canonical
