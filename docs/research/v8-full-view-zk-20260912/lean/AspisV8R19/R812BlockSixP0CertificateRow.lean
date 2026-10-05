import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R813FiniteFunctionExt39
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812BlockSixP0CertificateRow
open AspisV8R19.R813FiniteFunctionExt39
noncomputable section
abbrev M := ZMod 2147483647
def p0CertificateValues : Fin 39 → M := ![0,0,0,0,0,4320,21888,0,0,0,0,0,0,0,0,0,0,0,0,0,1610612724,1610612724,1758,13602,1073739662,1073723870,2147481010,2147463244,3366,27054,2147480131,2147313751,4323,227988,5274,254844,1610606082,0,0]
theorem certificate_p0_values : (fun j : Fin 39 => R747JointBlock39Preflight.A (⟨38,by decide⟩ : Fin 39) j) = p0CertificateValues := by
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
#print axioms certificate_p0_values
end
end AspisV8R19.R812BlockSixP0CertificateRow
