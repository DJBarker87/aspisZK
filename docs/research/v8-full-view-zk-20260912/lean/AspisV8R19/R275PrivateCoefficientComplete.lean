import AspisV8R19.R273PrivateCoefficientFallback
import AspisV8R19.R270PrivateCoefficientExecution

/-! Complete private coefficient constructor on an actual three-element
raw array. Canonical inputs are decoded and re-encoded exactly; every
noncanonical component follows the proved source Option fallback. -/
set_option autoImplicit false
namespace AspisV8R19.R275PrivateCoefficientComplete
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase (M31Exact CM31Exact QM31Exact P)
open AspisR156FullFreeze.aspis_core.field (CM31 QM31)
open AspisR264PrivateCoefficientRaw.circle_norm.joined_inverse.line_norm.r110_norm (Coeff110)
open ComplexBaseExecution (encodeBase eq_encodeBase)
open R273PrivateCoefficientFallback (canonC)
noncomputable section

def decodeC (x : CM31) : CM31Exact := ⟨(x.a.val : M31Exact),(x.b.val : M31Exact)⟩
def decodeQ (x : QM31) : QM31Exact := ⟨decodeC x.c0,decodeC x.c1⟩

theorem word_reencode (w : U32) (h : w.val<P) :
    encodeBase (w.val : M31Exact) = w :=
  (eq_encodeBase w (w.val : M31Exact) h rfl).symm

theorem complex_reencode (x : CM31) (h : canonC x) :
    R163ComplexExecution.encode (decodeC x) = x := by
  rcases h with ⟨ha,hb⟩
  cases x with
  | mk a b =>
    simp only [decodeC,R163ComplexExecution.encode]
    rw [word_reencode a ha,word_reencode b hb]

theorem quartic_reencode (x : QM31) (h : canonC x.c0 ∧ canonC x.c1) :
    R164ProductExecution.encode (decodeQ x) = x := by
  rcases h with ⟨ha,hb⟩
  cases x with
  | mk a b =>
    simp only [decodeQ,R164ProductExecution.encode]
    rw [complex_reencode a ha,complex_reencode b hb]

def canonTriple (a b c : QM31) : Prop :=
  canonC a.c0 ∧ canonC a.c1 ∧ canonC b.c0 ∧ canonC b.c1 ∧ canonC c.c0 ∧ canonC c.c1
instance canonTriple_decidable (a b c : QM31) : Decidable (canonTriple a b c) :=
  inferInstanceAs (Decidable (canonC a.c0 ∧ canonC a.c1 ∧
    canonC b.c0 ∧ canonC b.c1 ∧ canonC c.c0 ∧ canonC c.c1))

theorem coeff_new_complete (a b c : QM31) :
    Coeff110.new (Array.make 3#usize [a,b,c]) =
      .ok (if canonTriple a b c then
        some (R270PrivateCoefficientExecution.coefficients (decodeQ a) (decodeQ b) (decodeQ c))
        else none) := by
  by_cases h : canonTriple a b c
  · rw [if_pos h]
    rcases h with ⟨ha0,ha1,hb0,hb1,hc0,hc1⟩
    have ht := R270PrivateCoefficientExecution.coeff_new_exact (decodeQ a) (decodeQ b) (decodeQ c)
    rw [quartic_reencode a ⟨ha0,ha1⟩,quartic_reencode b ⟨hb0,hb1⟩,
      quartic_reencode c ⟨hc0,hc1⟩] at ht
    exact ht
  · rw [if_neg h]
    exact R273PrivateCoefficientFallback.coefficient_new_noncanonical a b c h

#print axioms word_reencode
#print axioms complex_reencode
#print axioms quartic_reencode
#print axioms coeff_new_complete
end
end AspisV8R19.R275PrivateCoefficientComplete
