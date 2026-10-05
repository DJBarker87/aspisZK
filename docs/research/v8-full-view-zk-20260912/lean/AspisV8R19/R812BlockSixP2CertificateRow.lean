import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R813FiniteFunctionExt39
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812BlockSixP2CertificateRow
open AspisV8R19.R813FiniteFunctionExt39
noncomputable section
abbrev M := ZMod 2147483647
def p2CertificateValues : Fin 39 → M := ![0,0,0,0,0,12960,65664,0,0,0,0,0,0,0,0,0,0,0,0,0,536870908,536870908,586,4534,1073741103,1073735839,2147482768,2147476846,1122,9018,2147482475,2147427015,1441,75996,1758,84948,536868694,0,0]
theorem certificate_p2_values : (fun j : Fin 39 => R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) j) = p2CertificateValues := by
  apply fin39_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
#print axioms certificate_p2_values
end
end AspisV8R19.R812BlockSixP2CertificateRow
