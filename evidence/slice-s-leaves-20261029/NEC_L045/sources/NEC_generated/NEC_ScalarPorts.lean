import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace NEC_ScalarPorts
open Aeneas Aeneas.Std
abbrev Word := AspisR1TerminalDecoder.aspis_core.field.M31

theorem u32_natural_injective (a b : U32) (same : a.val=b.val) : a=b :=
 UScalar.eq_of_val_eq same

theorem m31_natural_injective (a b : Word) (same : a.val=b.val) : a=b :=
 UScalar.eq_of_val_eq same

theorem u64_natural_injective (a b : U64) (same : a.val=b.val) : a=b :=
 UScalar.eq_of_val_eq same

/-- Native observation widens u32 to u64. The unchanged natural value is
its port; injectivity needs no M31 canonicality hypothesis. -/
theorem widened_word_injective (a b : Word) (nativeA nativeB : U64)
 (portA : nativeA.val=a.val) (portB : nativeB.val=b.val)
 (same : nativeA=nativeB) : a=b := by
 apply m31_natural_injective
 rw [←portA,←portB,same]

#print axioms u32_natural_injective
#print axioms m31_natural_injective
#print axioms u64_natural_injective
#print axioms widened_word_injective
end NEC_ScalarPorts
