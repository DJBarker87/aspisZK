import R1ConcreteBinding
import R0C.ModuloCounting

/-! Independent-answer bounds for the four concrete opening bad sets.
The algebraic data are fixed parameters of these statements; this file does
not establish their causal availability in a transcript or a Fiat--Shamir
law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OpeningSamplerBound

open AspisCircleGroupOrder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisR1.ConcreteBinding
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open Polynomial

variable {A E : Type} [Fintype A] [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

def sample (input : A ≃ Fin (2^256)) (output : Fin (P^8) ≃ E)
    (a : A) : E :=
  output (R0C.ModuloCounting.reduce (by norm_num [P]) (input a))

def atom : ℚ := (((2^256 / P^8 + 1 : Nat) : ℚ) / (2^256 : Nat))

/-- The zero-excluding map used by the gamma sampler. -/
def gammaNZ (input : A ≃ Fin (2^256))
    (outputNZ : Fin (P^8-1) ≃ {x : E // x ≠ 0}) (a : A) : {x : E // x ≠ 0} :=
  outputNZ (R0C.ModuloCounting.reduce (by norm_num [P]) (input a))

def gammaSample (input : A ≃ Fin (2^256))
    (outputNZ : Fin (P^8-1) ≃ {x : E // x ≠ 0}) (a : A) : E :=
  (gammaNZ input outputNZ a).val

theorem gammaSample_ne_zero (input : A ≃ Fin (2^256))
    (outputNZ : Fin (P^8-1) ≃ {x : E // x ≠ 0}) (a : A) :
    gammaSample input outputNZ a ≠ 0 := (gammaNZ input outputNZ a).property

def gammaAtom : ℚ :=
  (((2^256 / (P^8-1) + 1 : Nat) : ℚ) / (2^256 : Nat))

private theorem set_mass_le (input : A ≃ Fin (2^256))
    (output : Fin (P^8) ≃ E) (S : Finset E) (C : ℚ)
    (hcard : (S.card : ℚ) ≤ C) :
    mean (fun a : A => indicator (sample input output a ∈ S)) ≤ C * atom := by
  have hatom : 0 ≤ atom := by
    unfold atom
    apply div_nonneg
    · exact_mod_cast Nat.zero_le (2^256 / P^8 + 1)
    · exact_mod_cast (Nat.zero_le (2^256))
  have hmass := R0C.ModuloCounting.event_mass_le
    (sample input output) atom
    (fun y => R0C.ModuloCounting.encoded_mass_le
      (by norm_num [P]) input output y) S
  calc
    _ ≤ (S.card : ℚ) * atom := hmass
    _ ≤ C * atom := mul_le_mul_of_nonneg_right hcard hatom

theorem gamma_mass_le (input : A ≃ Fin (2^256))
    (outputNZ : Fin (P^8-1) ≃ {x : E // x ≠ 0}) (W : Fin 29 → InitialWord E)
    (F : Fin 6 → Functional E) (Y : Fin 6 → Fin 29 → E) :
    mean (fun a : A => indicator
      (gammaSample input outputNZ a ∈ ConcreteBinding.gammaBad W F Y)) ≤
      (336869026622539 : ℚ) * gammaAtom := by
  letI : Nonempty A := ⟨input.symm 0⟩
  have hc := ConcreteBinding.gammaBad_card W F Y
  have hgammaAtom : 0 ≤ gammaAtom := by
    unfold gammaAtom
    apply div_nonneg
    · exact_mod_cast Nat.zero_le (2^256 / (P^8 - 1) + 1)
    · exact_mod_cast Nat.zero_le (2^256)
  have hmass : ∀ y : E, mean (fun a : A =>
      indicator (gammaSample input outputNZ a = y)) ≤ gammaAtom := by
    intro y
    by_cases hy : y = 0
    · subst y
      have he (a : A) : indicator (gammaSample input outputNZ a = 0) = 0 := by
        simp only [indicator, if_neg (gammaSample_ne_zero input outputNZ a)]
      rw [mean_congr he, mean_const]
      exact hgammaAtom
    · let y' : {x : E // x ≠ 0} := ⟨y, hy⟩
      have he (a : A) : gammaSample input outputNZ a = y ↔
          gammaNZ input outputNZ a = y' := by
        constructor
        · intro h
          exact Subtype.ext h
        · intro h
          exact congrArg Subtype.val h
      have hm := R0C.ModuloCounting.encoded_mass_le
        (by norm_num [P]) input outputNZ y'
      have hm' : mean (fun a : A => indicator
          (gammaNZ input outputNZ a = y')) ≤ gammaAtom := by
        simpa only [gammaNZ, gammaAtom] using hm
      exact (mean_congr (fun a => FS.indicator_iff (he a))).le.trans hm'
  have hmassEvent := R0C.ModuloCounting.event_mass_le
    (gammaSample input outputNZ) gammaAtom hmass (ConcreteBinding.gammaBad W F Y)
  have hcard : ((ConcreteBinding.gammaBad W F Y).card : ℚ) ≤ 336869026622539 := by
    exact_mod_cast hc
  calc
    _ ≤ ((ConcreteBinding.gammaBad W F Y).card : ℚ) * gammaAtom := hmassEvent
    _ ≤ (336869026622539 : ℚ) * gammaAtom :=
      mul_le_mul_of_nonneg_right hcard hgammaAtom

theorem kappa_mass_le (input : A ≃ Fin (2^256))
    (output : Fin (P^8) ≃ E) (W : Fin 29 → InitialWord E)
    (F : Fin 6 → Functional E) (F0 : Functional E)
    (Y : Fin 6 → Fin 29 → E) (c0 gamma : E) :
    mean (fun a : A => indicator
      (sample input output a ∈ ConcreteBinding.kappaBad W F F0 Y c0 gamma)) ≤
      (600 : ℚ) * atom := by
  have hc := ConcreteBinding.kappaBad_card W F F0 Y c0 gamma
  have hcard : ((ConcreteBinding.kappaBad W F F0 Y c0 gamma).card : ℚ) ≤ 600 := by
    exact_mod_cast hc
  exact set_mass_le input output _ 600 hcard

theorem first_mass_le (input : A ≃ Fin (2^256))
    (output : Fin (P^8) ≃ E) (W : Fin 29 → InitialWord E)
    (gamma : E) (w : Fin 1024 → E) (p0 : E[X])
    (hdegree : p0.natDegree ≤ 6) :
    mean (fun a : A => indicator
      (sample input output a ∈ ConcreteBinding.firstBad W gamma w p0)) ≤
      (9396508281846 : ℚ) * atom := by
  have hc := ConcreteBinding.firstBad_card W gamma w p0 hdegree
  have hcard : ((ConcreteBinding.firstBad W gamma w p0).card : ℚ) ≤ 9396508281846 := by
    exact_mod_cast hc
  exact set_mass_le input output _ 9396508281846 hcard

theorem second_mass_le (input : A ≃ Fin (2^256))
    (output : Fin (P^8) ≃ E) (W : Fin 29 → InitialWord E)
    (V : FinalWord E) (gamma alpha0 : E) (w : Fin 1024 → E) (p1 : E[X])
    (hdegree : p1.natDegree ≤ 6) :
    mean (fun a : A => indicator
      (sample input output a ∈ ConcreteBinding.secondBad W V gamma alpha0 w p1)) ≤
      (9396508281846 : ℚ) * atom := by
  have hc := ConcreteBinding.secondBad_card W V gamma alpha0 w p1 hdegree
  have hcard : ((ConcreteBinding.secondBad W V gamma alpha0 w p1).card : ℚ) ≤
      9396508281846 := by exact_mod_cast hc
  exact set_mass_le input output _ 9396508281846 hcard

def openingCap : ℚ :=
  (336869026622539 : ℚ) * gammaAtom +
    (600 + 2 * 9396508281846 : ℚ) * atom

theorem openingCap_lt_two_neg_199 : openingCap < 1 / (2^199 : ℚ) := by
  norm_num [openingCap, gammaAtom, atom, P]

#print axioms gamma_mass_le
#print axioms gammaSample_ne_zero
#print axioms kappa_mass_le
#print axioms first_mass_le
#print axioms second_mass_le
#print axioms openingCap_lt_two_neg_199

end AspisR1.OpeningSamplerBound
end
