import AspisV8R19.R721SelectedRowLowerBound
import AspisV8R19.HighQueryGCore

set_option autoImplicit false
namespace AspisV8R19.R723ActiveKernelSupport
open AspisV8R17 AspisR19
open AspisV8R19.R721SelectedRowLowerBound
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R707FullActiveDeterminant

variable {F : Type*} [CommRing F]

theorem active_kernel_support (half a b c : F) (q : Nat → F)
    (hq : ∀ n, 108 ≤ n → q n = 0) (i : J) :
    sourceChord half q a b c (rowCode i) = 0 := by
  apply HighQueryGCore.sourceChord_support half q 54 hq a b c (rowCode i)
  have h := rowCode_ge_114 i
  omega

#print axioms active_kernel_support
end AspisV8R19.R723ActiveKernelSupport
