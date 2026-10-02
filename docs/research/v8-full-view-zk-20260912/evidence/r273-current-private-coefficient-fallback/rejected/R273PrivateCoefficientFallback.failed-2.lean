import AspisR264PrivateCoefficientRaw
import AspisV8R19.R260PrivateInputExecution
import AspisV8R19.R265PrivateNormClosures

/-! Fallback behavior of the actual private coefficient constructor on raw
inputs: if any component fails the selected canonical input check, its
source-bound Option flow returns none. No arithmetic failure is assumed. -/
set_option autoImplicit false
namespace AspisV8R19.R273PrivateCoefficientFallback
open Aeneas Aeneas.Std Result ControlFlow
open AspisR156FullFreeze.aspis_core.field (QM31 CM31)
open AspisV8R15.ExactTowerBase (P)
open AspisR259PrivateInputRaw
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm (C)
open AspisR264PrivateCoefficientRaw.circle_norm.joined_inverse.line_norm.r110_norm (Coeff110)
noncomputable section

def canonC (x : CM31) : Prop := x.a.val < P ∧ x.b.val < P

theorem raw_c_input (x : CM31) :
    AspisR259PrivateInputRaw.circle_norm.joined_inverse.line_norm.r110_norm.C.input x = .ok (if canonC x then some (x.a,x.b) else none) := by
  simpa [canonC] using R260PrivateInputExecution.input_complete x

theorem coefficient_new_noncanonical
    (a b c : QM31)
    (hbad : ¬ (canonC a.c0 ∧ canonC a.c1 ∧
      canonC b.c0 ∧ canonC b.c1 ∧ canonC c.c0 ∧ canonC c.c1)) :
    Coeff110.new (Array.make 3#usize [a,b,c]) = .ok none := by
  by_cases h0 : canonC a.c0
  · by_cases h1 : canonC a.c1
    · by_cases h2 : canonC b.c0
      · by_cases h3 : canonC b.c1
        · by_cases h4 : canonC c.c0
          · by_cases h5 : canonC c.c1
            · have hgood : canonC a.c0 ∧ canonC a.c1 ∧
                canonC b.c0 ∧ canonC b.c1 ∧ canonC c.c0 ∧ canonC c.c1 :=
                  ⟨h0,h1,h2,h3,h4,h5⟩
              exact False.elim (hbad hgood)
            · simp [Coeff110.new, Array.make, Array.index_usize, raw_c_input,
                h0, h1, h2, h3, h4, h5,
                R260PrivateInputExecution.branch_none,
                R260PrivateInputExecution.branch_some,
                R260PrivateInputExecution.residual_none,
                bind_tc_ok]
          · simp [Coeff110.new, Array.make, Array.index_usize, raw_c_input,
              h0, h1, h2, h3, h4,
              R260PrivateInputExecution.branch_none,
              R260PrivateInputExecution.branch_some,
              R260PrivateInputExecution.residual_none,
              bind_tc_ok]
        · simp [Coeff110.new, Array.make, Array.index_usize, raw_c_input,
            h0, h1, h2, h3,
            R260PrivateInputExecution.branch_none,
            R260PrivateInputExecution.branch_some,
            R260PrivateInputExecution.residual_none,
            bind_tc_ok]
      · simp [Coeff110.new, Array.make, Array.index_usize, raw_c_input,
          h0, h1, h2,
          R260PrivateInputExecution.branch_none,
          R260PrivateInputExecution.branch_some,
          R260PrivateInputExecution.residual_none,
          bind_tc_ok]
    · simp [Coeff110.new, Array.make, Array.index_usize, raw_c_input,
        h0, h1,
        R260PrivateInputExecution.branch_none,
        R260PrivateInputExecution.branch_some,
        R260PrivateInputExecution.residual_none,
        bind_tc_ok]
  · simp [Coeff110.new, Array.make, Array.index_usize, raw_c_input,
      h0,
      R260PrivateInputExecution.branch_none,
      R260PrivateInputExecution.branch_some,
      R260PrivateInputExecution.residual_none,
      bind_tc_ok]

#print axioms raw_c_input
#print axioms coefficient_new_noncanonical
end
end AspisV8R19.R273PrivateCoefficientFallback
