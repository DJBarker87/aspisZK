import M31ActualWideSamplerTapeLaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
namespace M31RetryOutputFiber

open M31AcceptFiber FSRetryOutputUniformity
attribute [local irreducible] actualEightWideSampler

abbrev WidePairInput := EightRetryInputs × EightRetryInputs
abbrev WidePairOutput := WideExactOutput × WideExactOutput

def actualWidePairSampler (x : WidePairInput) : Option WidePairOutput :=
  match actualEightWideSampler x.1, actualEightWideSampler x.2 with
  | some a, some b => some (a, b)
  | _, _ => none

abbrev ActualWidePairSuccessInput :=
  {x : WidePairInput // ∃ y : WidePairOutput, actualWidePairSampler x = some y}

abbrev ActualWidePairFiber (y : WidePairOutput) :=
  {x : WidePairInput // actualWidePairSampler x = some y}

theorem actualWidePairSampler_some_iff (x : WidePairInput) (y : WidePairOutput) :
    actualWidePairSampler x = some y ↔
      actualEightWideSampler x.1 = some y.1 ∧
      actualEightWideSampler x.2 = some y.2 := by
  cases y with
  | mk a b =>
    cases h1 : actualEightWideSampler x.1 <;>
      cases h2 : actualEightWideSampler x.2 <;>
      simp only [actualWidePairSampler, h1, h2, Option.some.injEq]
    case some.some va vb =>
      constructor
      · intro h
        cases h
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        rfl

theorem actualWidePairSampler_none_iff (x : WidePairInput) :
    actualWidePairSampler x = none ↔
      actualEightWideSampler x.1 = none ∨ actualEightWideSampler x.2 = none := by
  cases h1 : actualEightWideSampler x.1 <;>
    cases h2 : actualEightWideSampler x.2 <;>
    simp [actualWidePairSampler, h1, h2]

noncomputable def actualWidePairSuccessEquiv : ActualWidePairSuccessInput ≃
    (ActualWideSuccessInput × ActualWideSuccessInput) where
  toFun x := by
    classical
    let y := Classical.choose x.2
    have hy := Classical.choose_spec x.2
    have hp := (actualWidePairSampler_some_iff x.1 y).mp hy
    exact ⟨⟨x.1.1, ⟨y.1, hp.1⟩⟩, ⟨x.1.2, ⟨y.2, hp.2⟩⟩⟩
  invFun z := by
    refine ⟨(z.1.1, z.2.1), ?_⟩
    obtain ⟨a, ha⟩ := z.1.2
    obtain ⟨b, hb⟩ := z.2.2
    exact ⟨(a,b), (actualWidePairSampler_some_iff _ _).mpr ⟨ha,hb⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

def actualWidePairFiberEquiv (y : WidePairOutput) :
    ActualWidePairFiber y ≃
      (actualWideOutputFiber y.1 × actualWideOutputFiber y.2) where
  toFun x :=
    ⟨⟨x.1.1, (actualWidePairSampler_some_iff x.1 y).mp x.2 |>.1⟩,
     ⟨x.1.2, (actualWidePairSampler_some_iff x.1 y).mp x.2 |>.2⟩⟩
  invFun z := by
    refine ⟨(z.1.1,z.2.1), ?_⟩
    exact (actualWidePairSampler_some_iff _ _).mpr ⟨z.1.2,z.2.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem actualWidePairFiber_card (y : WidePairOutput) :
    Nat.card (ActualWidePairFiber y) = limbBaseCount ^ 16 := by
  calc
    Nat.card (ActualWidePairFiber y) =
      Nat.card (actualWideOutputFiber y.1 × actualWideOutputFiber y.2) :=
        Nat.card_congr (actualWidePairFiberEquiv y)
    _ = Nat.card (actualWideOutputFiber y.1) *
        Nat.card (actualWideOutputFiber y.2) := by
      classical
      letI : Fintype (actualWideOutputFiber y.1) := inferInstance
      letI : Fintype (actualWideOutputFiber y.2) := inferInstance
      rw [Nat.card_eq_fintype_card, Fintype.card_prod,
        ← Nat.card_eq_fintype_card (α := actualWideOutputFiber y.1),
        ← Nat.card_eq_fintype_card (α := actualWideOutputFiber y.2)]
    _ = limbBaseCount ^ 16 := by
      rw [actualWideOutputFiber_card, actualWideOutputFiber_card]
      rw [← pow_add]

abbrev ActualWidePairInputTape (n : Nat) := Fin n → WidePairInput
abbrev ActualWidePairOutputTape (n : Nat) := Fin n → WidePairOutput
abbrev ActualWidePairSuccessTape (n : Nat) :=
  {xs : ActualWidePairInputTape n //
    ∀ i : Fin n, ∃ y : WidePairOutput, actualWidePairSampler (xs i) = some y}
abbrev ActualWidePairOutputFiberTape (n : Nat) (ys : ActualWidePairOutputTape n) :=
  {xs : ActualWidePairInputTape n //
    ∀ i : Fin n, actualWidePairSampler (xs i) = some (ys i)}

def actualWidePairSuccessTapeEquiv (n : Nat) : ActualWidePairSuccessTape n ≃
    ((i : Fin n) → ActualWidePairSuccessInput) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by funext i; apply Subtype.ext; rfl

def actualWidePairFiberTapeEquiv (n : Nat) (ys : ActualWidePairOutputTape n) :
    ActualWidePairOutputFiberTape n ys ≃ ((i : Fin n) → ActualWidePairFiber (ys i)) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by funext i; apply Subtype.ext; rfl

theorem actualWidePairFiberTape_card (n : Nat) (ys : ActualWidePairOutputTape n) :
    Nat.card (ActualWidePairOutputFiberTape n ys) = limbBaseCount ^ (16*n) := by
  classical
  calc
    _ = Nat.card ((i : Fin n) → ActualWidePairFiber (ys i)) :=
      Nat.card_congr (actualWidePairFiberTapeEquiv n ys)
    _ = ∏ i : Fin n, Nat.card (ActualWidePairFiber (ys i)) := Nat.card_pi
    _ = ∏ _i : Fin n, limbBaseCount ^ 16 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact actualWidePairFiber_card (ys i)
    _ = (limbBaseCount ^ 16) ^ n := by simp
    _ = limbBaseCount ^ (16*n) := by rw [pow_mul]

theorem actualWidePairSuccessTape_card (n : Nat) :
    Nat.card (ActualWidePairSuccessTape n) =
      ((P31 ^ 8 * limbBaseCount ^ 8) ^ 2) ^ n := by
  classical
  calc
    _ = Nat.card ((i : Fin n) → ActualWidePairSuccessInput) :=
      Nat.card_congr (actualWidePairSuccessTapeEquiv n)
    _ = ∏ _i : Fin n, Nat.card ActualWidePairSuccessInput := Nat.card_pi
    _ = ∏ _i : Fin n, (P31 ^ 8 * limbBaseCount ^ 8) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Nat.card_congr actualWidePairSuccessEquiv]
      classical
      rw [Nat.card_eq_fintype_card, Fintype.card_prod,
        ← Nat.card_eq_fintype_card (α := ActualWideSuccessInput)]
      rw [actualWideSuccessInput_card, eightSuccess_count_eq_P31pow_mul_base]
      rw [pow_two]
    _ = ((P31 ^ 8 * limbBaseCount ^ 8) ^ 2) ^ n := by simp

theorem actualWidePairTape_conditional_uniform (n : Nat)
    (ys : ActualWidePairOutputTape n) :
    (Nat.card (ActualWidePairOutputFiberTape n ys) : ℚ) /
      (Nat.card (ActualWidePairSuccessTape n) : ℚ) =
        1 / (P31 : ℚ) ^ (16*n) := by
  rw [actualWidePairFiberTape_card, actualWidePairSuccessTape_card]
  have hP : (P31 : ℚ) ≠ 0 := by norm_num [P31]
  have hB : (limbBaseCount : ℚ) ≠ 0 := by
    have hbase : 0 < limbBaseCount := by
      have h := scalar_success_count_eq_P31_mul_base
      rcases Nat.eq_zero_or_pos limbBaseCount with hz | hp
      · rw [hz] at h
        norm_num [P31] at h
      · exact hp
    exact_mod_cast Nat.ne_of_gt hbase
  push_cast
  change ((limbBaseCount : ℚ) ^ (16*n)) /
      ((((P31 : ℚ)^8 * (limbBaseCount : ℚ)^8)^2)^n) =
    1 / (P31 : ℚ)^(16*n)
  have hden : (((P31 : ℚ)^8 * (limbBaseCount : ℚ)^8)^2)^n =
      (P31 : ℚ)^(16*n) * (limbBaseCount : ℚ)^(16*n) := by
    rw [pow_mul, mul_pow]
    have hp : ((P31 : ℚ)^8)^(2*n) = (P31 : ℚ)^(16*n) := by
      rw [pow_mul, pow_mul]
      congr 1
      omega
    have hb : ((limbBaseCount : ℚ)^8)^(2*n) =
        (limbBaseCount : ℚ)^(16*n) := by
      rw [pow_mul, pow_mul]
      congr 1
      omega
    rw [hp, hb]
  rw [hden]
  field_simp [hP,hB]
  <;> ring

theorem nat_pow_sub_ratio (S T k : Nat) (hST : S ≤ T)
    (hT : (T : ℚ) ≠ 0) :
    ((T^k - S^k : Nat) : ℚ) / ((T^k : Nat) : ℚ) =
      1 - ((S : ℚ)/(T : ℚ))^k := by
  have hpow : S^k ≤ T^k := Nat.pow_le_pow_left hST k
  rw [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_pow]
  have hTp : (T:ℚ)^k ≠ 0 := pow_ne_zero k hT
  rw [div_pow]
  field_simp [hT,hTp]
  <;> ring

end M31RetryOutputFiber
