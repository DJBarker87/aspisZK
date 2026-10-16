import R1AllAddressFiatShamir
import FS2.DuplexTrace

/-! First-read collision bounds for arbitrary address types. A table has a
finite covering set before a bounded first read, even when the address space
is infinite. The output state space alone is finite. B parsed target maps,
the initial state and previous outputs cost (B+1)Q²/|A|; B=11 gives 12Q²/|A|.
This does not yet identify the eleven maps with the source's parsers. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.AllAddressCollision

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.UniformStateFirstHit

variable {I A O : Type} [DecidableEq I] [Fintype A] [Inhabited A]

/-- A finite cover of all defined table entries, with room for the current
first read. This condition concerns the table, not the next oracle answer. -/
def Small (T : Table I A) (Q : Nat) : Prop :=
  ∃ s : Finset I, s.card < Q ∧ ∀ b, T b ≠ none → b ∈ s

def bad {B : Nat} (iv : A) (pred : Fin B → I → Option A) (Q : Nat)
    (a : I) (T : Table I A) (f : A) : Prop :=
  Small T Q ∧ (f = iv ∨ (∃ b, T b = some f) ∨
    ∃ j : Fin B, ∃ b, (b = a ∨ T b ≠ none) ∧ pred j b = some f)

theorem finite_target_mass (s : Finset I) (pred : I → Option A) :
    mean (fun f : A => indicator (∃ b ∈ s, pred b = some f)) ≤
      (s.card : ℚ) / (Fintype.card A : ℚ) := by
  classical
  have h := mean_exists_prefix_le (fun f : A => some f)
    (by intro f g h; exact Option.some.inj h)
    (fun _ : {b // b ∈ s} => True) (fun b => pred b.val)
  have he (f : A) : (∃ b ∈ s, pred b = some f) ↔
      ∃ b : {b // b ∈ s}, True ∧ pred b.val = some f := by
    constructor
    · rintro ⟨b, hb, hp⟩; exact ⟨⟨b, hb⟩, trivial, hp⟩
    · rintro ⟨b, _, hp⟩; exact ⟨b.val, b.property, hp⟩
  rw [mean_congr (fun f => indicator_iff (he f))]
  simpa using h

theorem previous_outputs_mass (iv : A) (T : Table I A) (s : Finset I)
    (hcover : ∀ b, T b ≠ none → b ∈ s) :
    mean (fun f : A => indicator (f = iv ∨ ∃ b, T b = some f)) ≤
      ((s.card : ℚ) + 1) / (Fintype.card A : ℚ) := by
  classical
  have hcontain (f : A) : (∃ b, T b = some f) → ∃ b ∈ s, T b = some f := by
    rintro ⟨b, hb⟩
    exact ⟨b, hcover b (by rw [hb]; exact Option.some_ne_none _), hb⟩
  calc
    _ ≤ mean (fun f : A => indicator (f = iv) +
        indicator (∃ b ∈ s, T b = some f)) := by
      apply mean_mono
      intro f
      exact (indicator_mono (fun h => h.elim Or.inl (fun hb => Or.inr (hcontain f hb)))).trans
        (indicator_or_le _ _)
    _ = mean (fun f : A => indicator (f = iv)) +
        mean (fun f : A => indicator (∃ b ∈ s, T b = some f)) := mean_add _ _
    _ ≤ 1 / (Fintype.card A : ℚ) + (s.card : ℚ) / (Fintype.card A : ℚ) :=
      add_le_add (le_of_eq (mean_indicator_eq iv)) (finite_target_mass s T)
    _ = _ := by ring

theorem parsed_target_mass (pred : I → Option A) (a : I) (T : Table I A)
    (s : Finset I) (hcover : ∀ b, T b ≠ none → b ∈ s) :
    mean (fun f : A => indicator
      (∃ b, (b = a ∨ T b ≠ none) ∧ pred b = some f)) ≤
      ((s.card : ℚ) + 1) / (Fintype.card A : ℚ) := by
  classical
  calc
    _ ≤ mean (fun f : A => indicator (∃ b ∈ insert a s, pred b = some f)) := by
      apply mean_mono
      intro f
      apply indicator_mono
      rintro ⟨b, hb, hp⟩
      refine ⟨b, ?_, hp⟩
      rcases hb with rfl | hb
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hcover b hb)
    _ ≤ ((insert a s).card : ℚ) / (Fintype.card A : ℚ) :=
      finite_target_mass (insert a s) pred
    _ ≤ ((s.card : ℚ) + 1) / (Fintype.card A : ℚ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_insert_le a s

theorem density {B : Nat} (iv : A) (pred : Fin B → I → Option A)
    (Q : Nat) (a : I) (T : Table I A) :
    mean (fun f : A => indicator (bad iv pred Q a T f)) ≤
      ((B : ℚ) + 1) * Q / (Fintype.card A : ℚ) := by
  classical
  have hden : (0 : ℚ) < (Fintype.card A : ℚ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (show Nonempty A from ⟨default⟩))
  by_cases hsmall : Small T Q
  · obtain ⟨s, hs, hcover⟩ := hsmall
    have hcard : (s.card : ℚ) + 1 ≤ (Q : ℚ) := by
      exact_mod_cast Nat.succ_le_of_lt hs
    have hout : mean (fun f : A => indicator (f = iv ∨ ∃ b, T b = some f)) ≤
        (Q : ℚ) / (Fintype.card A : ℚ) :=
      (previous_outputs_mass iv T s hcover).trans
        (div_le_div_of_nonneg_right hcard (by positivity))
    have hpred : mean (fun f : A => indicator
        (∃ j : Fin B, ∃ b, (b = a ∨ T b ≠ none) ∧ pred j b = some f)) ≤
        (B : ℚ) * ((Q : ℚ) / (Fintype.card A : ℚ)) := by
      have h := mean_firstHit_union_le
        (fun j : Fin B => fun f : A => ∃ b, (b = a ∨ T b ≠ none) ∧ pred j b = some f)
        (fun _ => (Q : ℚ) / (Fintype.card A : ℚ))
        (fun j => (parsed_target_mass (pred j) a T s hcover).trans
          (div_le_div_of_nonneg_right hcard (by positivity)))
      simpa using h
    calc
      _ ≤ mean (fun f : A => indicator (f = iv ∨ ∃ b, T b = some f) +
          indicator (∃ j : Fin B, ∃ b, (b = a ∨ T b ≠ none) ∧ pred j b = some f)) := by
        apply mean_mono
        intro f
        apply le_trans (indicator_mono ?_) (indicator_or_le _ _)
        rintro ⟨_, h | h | h⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      _ = mean (fun f : A => indicator (f = iv ∨ ∃ b, T b = some f)) +
          mean (fun f : A => indicator
            (∃ j : Fin B, ∃ b, (b = a ∨ T b ≠ none) ∧ pred j b = some f)) := mean_add _ _
      _ ≤ (Q : ℚ) / (Fintype.card A : ℚ) +
          (B : ℚ) * ((Q : ℚ) / (Fintype.card A : ℚ)) := add_le_add hout hpred
      _ = _ := by ring
  · have he : ∀ f : A, indicator (bad iv pred Q a T f) = 0 := by
      intro f
      simp only [bad, hsmall, false_and, indicator_false]
    rw [mean_congr he, mean_const]
    apply div_nonneg
    · positivity
    · exact le_of_lt hden

theorem mass {B : Nat} (iv : A) (pred : Fin B → I → Option A)
    (Q : Nat) (p : Program I A O)
    (hQ : ∀ H : I → A, firstReads emptyTable (eval H p).1 ≤ Q) :
    lazyMean p emptyTable (fun v => indicator (hitsBad (bad iv pred Q) emptyTable v.1)) ≤
      ((B : ℚ) + 1) * (Q : ℚ)^2 / (Fintype.card A : ℚ) := by
  have hN : FirstReadsBound p (emptyTable : Table I A) Q := by
    apply firstReadsBound_of_traces
    intro H
    exact hQ H
  have hden : (0 : ℚ) < (Fintype.card A : ℚ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (show Nonempty A from ⟨default⟩))
  have h := FS.lemmaA p emptyTable Q (bad iv pred Q)
    (((B : ℚ) + 1) * Q / (Fintype.card A : ℚ)) (by
      apply div_nonneg
      · positivity
      · exact le_of_lt hden)
    (density iv pred Q) hN
  calc
    _ ≤ (Q : ℚ) * (((B : ℚ) + 1) * Q / (Fintype.card A : ℚ)) := h
    _ = _ := by ring

#print axioms finite_target_mass
#print axioms previous_outputs_mass
#print axioms parsed_target_mass
#print axioms density
#print axioms mass
end AspisR1.AllAddressCollision
end
