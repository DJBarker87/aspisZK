import NDO_JHe_SHAEquations0
import NDO_JHe_SHAEquations1
import NDO_JHe_SHAEquations2
set_option autoImplicit false
namespace AspisR1
/-- Exactly 453 concrete batch SHA equations as three finite law families. -/
class JHe_SHARealization : Prop where
  tree0 : ∀ i : Fin 157, JFp_SHADigest.digest (JHe_SHAInputs0.input i)=JHe_SHAInputs0.expected i
  tree1 : ∀ i : Fin 157, JFp_SHADigest.digest (JHe_SHAInputs1.input i)=JHe_SHAInputs1.expected i
  tree2 : ∀ i : Fin 139, JFp_SHADigest.digest (JHe_SHAInputs2.input i)=JHe_SHAInputs2.expected i
end AspisR1
