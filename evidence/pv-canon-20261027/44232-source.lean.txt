import R1Z.PV_Canon_CSquare
import R1Z.PV_Canon_CMul
import R1Z.PV_Canon_CAdd
import R1Z.PV_Canon_CDouble
import R1Z.PV_Canon_MulR
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 theorem current_qsquare (x : aspis_core.field.QM31) :
    ∃ z, ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square x = .ok z ∧ Q z := by
  obtain ⟨a,ha,hca⟩ := current_csquare x.c0
  obtain ⟨b,hb,hcb⟩ := current_csquare x.c1
  obtain ⟨c,hc,hcc⟩ := current_mulr b hcb
  obtain ⟨d,hd,hcd⟩ := current_cadd a c hca hcc
  obtain ⟨e,he,hce⟩ := current_cmul x.c0 x.c1
  obtain ⟨f,hf,hcf⟩ := current_cdouble e hce
  refine ⟨⟨d,f⟩,?_,hcd,hcf⟩
  simp only [ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square,
    ha,hb,hc,hd,he,hf,bind_tc_ok]
#print axioms current_qsquare
end R1Z.PV_Canon
