import NDO_JHm_Dot0_7
import NDO_JHm_Dot1_7
import NDO_JHm_Dot2_7
import NDO_JHm_Dot3_7
import NDO_JHm_Dot4_7
import NDO_JHm_Dot5_7
import NDO_JHl_ClaimKappa
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Dots
open JHm_Arithmetic
def value (p : Nat) : FE := match p with
  | 0 => JHm_Dot0_7.h00
  | 1 => JHm_Dot1_7.h00
  | 2 => JHm_Dot2_7.h00
  | 3 => JHm_Dot3_7.h00
  | 4 => JHm_Dot4_7.h00
  | 5 => JHm_Dot5_7.h00
  | _ => 0
theorem source (p : Fin 6) : horner gamma (JHm_Arithmetic.row p.val)=value p.val := by
  fin_cases p
  · exact JHm_Dot0_7.source
  · exact JHm_Dot1_7.source
  · exact JHm_Dot2_7.source
  · exact JHm_Dot3_7.source
  · exact JHm_Dot4_7.source
  · exact JHm_Dot5_7.source
#print axioms source
def term (i : Nat) : FE := JHl_ClaimKappa.value (i+1)*value i
end AspisR1.JHm_Dots
end
