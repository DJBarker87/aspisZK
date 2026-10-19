import M31PairedWideSamplerLaw
import FiniteOptionSamplerComposition
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace M31RetryOutputFiber

open AspisR1.FiniteOptionSamplerComposition
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open M31AcceptFiber FSRetryOutputUniformity

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev PairedRawTape (n : Nat) := ActualWidePairInputTape n
abbrev PairedOutputTape (n : Nat) := ActualWidePairOutputTape n

def actualPairedTapeSampler (n : Nat) : PairedRawTape n → Option (PairedOutputTape n) :=
  actualWidePairSamplerTape n

abbrev PairedTapeSuccess (n : Nat) := ActualWidePairSuccessTape n
abbrev PairedTapeFiber (n : Nat) (ys : PairedOutputTape n) :=
  ActualWidePairOutputFiberTape n ys

private noncomputable def pairedTapeSomeSubtypeEquiv (n : Nat) :
    {xs : PairedRawTape n // (actualPairedTapeSampler n xs).isSome} ≃ PairedTapeSuccess n where
  toFun x := by
    classical
    have hys : ∃ ys, actualPairedTapeSampler n x.1 = some ys := by
      cases hs : actualPairedTapeSampler n x.1 with
      | none =>
        have hfalse : False := by simpa [hs] using x.2
        exact False.elim hfalse
      | some ys => exact ⟨ys, rfl⟩
    let ys := Classical.choose hys
    have hyspec := Classical.choose_spec hys
    refine ⟨x.1, ?_⟩
    intro i
    exact ⟨ys i, (actualWidePairSamplerTape_some_iff n x.1 ys).mp hyspec i⟩
  invFun x := by
    refine ⟨x.1, ?_⟩
    apply Option.isSome_iff_exists.mpr
    refine ⟨fun i => (actualWidePairSampler (x.1 i)).getD (0,0), ?_⟩
    apply (actualWidePairSamplerTape_some_iff n x.1 _).mpr
    intro i
    obtain ⟨y,hy⟩ := x.2 i
    cases hs : actualWidePairSampler (x.1 i) with
    | none => rw [hs] at hy; cases hy
    | some z =>
      have hz : z = y := Option.some.inj (hs.symm.trans hy)
      simpa [hs, hz]
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

private noncomputable def pairedTapeFiberSubtypeEquiv (n : Nat) (ys : PairedOutputTape n) :
    {xs : PairedRawTape n // actualPairedTapeSampler n xs = some ys} ≃ PairedTapeFiber n ys where
  toFun x := ⟨x.1, fun i => (actualWidePairSamplerTape_some_iff n x.1 ys).mp x.2 i⟩
  invFun x := ⟨x.1, (actualWidePairSamplerTape_some_iff n x.1 ys).mpr x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

private theorem pairedTapeSuccess_count (n : Nat) :
    Fintype.card {xs : PairedRawTape n // (actualPairedTapeSampler n xs).isSome} =
      Nat.card (PairedTapeSuccess n) := by
  classical
  letI : Fintype {xs : PairedRawTape n // (actualPairedTapeSampler n xs).isSome} := inferInstance
  letI : Fintype (PairedTapeSuccess n) := Fintype.ofFinite _
  calc
    Fintype.card {xs : PairedRawTape n // (actualPairedTapeSampler n xs).isSome} =
        Nat.card {xs : PairedRawTape n // (actualPairedTapeSampler n xs).isSome} :=
      (Nat.card_eq_fintype_card).symm
    _ = Nat.card (PairedTapeSuccess n) := Nat.card_congr (pairedTapeSomeSubtypeEquiv n)

private theorem pairedTapeFiber_count (n : Nat) (ys : PairedOutputTape n) :
    Fintype.card {xs : PairedRawTape n // actualPairedTapeSampler n xs = some ys} =
      Nat.card (PairedTapeFiber n ys) := by
  classical
    letI : Fintype {xs : PairedRawTape n // actualPairedTapeSampler n xs = some ys} := inferInstance
  letI : Fintype (PairedTapeFiber n ys) := Fintype.ofFinite _
  calc
    Fintype.card {xs : PairedRawTape n // actualPairedTapeSampler n xs = some ys} =
        Nat.card {xs : PairedRawTape n // actualPairedTapeSampler n xs = some ys} :=
      (Nat.card_eq_fintype_card).symm
    _ = Nat.card (PairedTapeFiber n ys) := Nat.card_congr (pairedTapeFiberSubtypeEquiv n ys)

private theorem pairedTapeOutput_count (n : Nat) :
    Fintype.card (PairedOutputTape n) = Nat.card (PairedOutputTape n) := by
  classical
  letI : Fintype (PairedOutputTape n) := inferInstance
  exact Nat.card_eq_fintype_card.symm

theorem actualPairedTape_output_mass_le_uniform (n : Nat) :
    ∀ ys : PairedOutputTape n,
      mean (fun xs : PairedRawTape n => indicator (actualPairedTapeSampler n xs = some ys)) ≤
        1 / (Fintype.card (PairedOutputTape n) : ℚ) := by
  classical
  letI : Fintype (PairedRawTape n) := inferInstance
  letI : Nonempty (PairedRawTape n) := inferInstance
  letI : Fintype (PairedOutputTape n) := inferInstance
  apply output_mass_le_uniform_of_conditional (actualPairedTapeSampler n)
  · have hsuccess : 0 < Nat.card (PairedTapeSuccess n) := by
      rw [actualWidePairSuccessTape_card]
      have hp : 0 < P31 := by norm_num [P31]
      have hb : 0 < limbBaseCount := by
        have hs := scalar_success_count_eq_P31_mul_base
        by_contra hn
        have hz : limbBaseCount = 0 := Nat.eq_zero_of_not_pos hn
        rw [hz] at hs
        norm_num [P31] at hs
      positivity
    have hfilter : (Finset.univ.filter
        (fun xs : PairedRawTape n => (actualPairedTapeSampler n xs).isSome)).card =
        Nat.card (PairedTapeSuccess n) := by
      rw [← Fintype.card_subtype]
      exact pairedTapeSuccess_count n
    rw [hfilter]
    exact_mod_cast hsuccess
  · intro ys
    have hcond := actualWidePairTape_conditional_uniform n ys
    have hfiber : (Finset.univ.filter
        (fun x : PairedRawTape n => actualPairedTapeSampler n x = some ys)).card =
          Nat.card (PairedTapeFiber n ys) := by
      rw [← Fintype.card_subtype]
      convert pairedTapeFiber_count n ys using 1 <;> congr 3 <;> all_goals ext x <;> simp
    have hsuccess : (Finset.univ.filter
        (fun x : PairedRawTape n => (actualPairedTapeSampler n x).isSome)).card =
          Nat.card (PairedTapeSuccess n) := by
      rw [← Fintype.card_subtype]
      convert pairedTapeSuccess_count n using 1 <;> congr 3 <;> all_goals ext x <;> simp
    have hratio := congrArg₂ (fun a b : Nat => (a : ℚ) / (b : ℚ)) hfiber hsuccess
    have hmass := hratio.trans hcond
    rw [pairedTapeOutput_count n]
    exact hmass

#print axioms pairedTapeSomeSubtypeEquiv
#print axioms pairedTapeFiberSubtypeEquiv
#print axioms actualPairedTape_output_mass_le_uniform

end
end M31RetryOutputFiber
