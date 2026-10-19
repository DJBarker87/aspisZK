import R0P.SemClosed
import R0P.SemBadSets
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The 24 semantic challenge rounds of the fixed pair-forest model.

Challenge order follows the lead's FS integration design: λ, χ, θ,
ten zerocheck coordinates, μ, then ten sumcheck challenges. The α event
is literally the recursive `Sumcheck.badAlpha` disjunct; the already
checked prover degree is used only for its cardinality bound. The λ event
uses the fixed leading coefficient of `LogUpAssembly.productDifference`.
No probability claim or Rust-to-model refinement is asserted here.
-/
set_option autoImplicit false

namespace R0P.Sumcheck
open Polynomial

variable {K : Type} [Field K]

/-- The honest partial-sum function at a specified round and prefix.
The recursion restricts exactly one leading coordinate per prefix entry. -/
def alphaRoundPartial : (n : Nat) → ((Fin n → K) → K) →
    (i : Fin n) → (Fin i.val → K) → K → K
  | 0, _, i => i.elim0
  | n+1, G, i => Fin.cases
      (fun _ x => bsum n (fun v => G (Fin.cons x v)))
      (fun j pref x => alphaRoundPartial n
        (fun v => G (Fin.cons (pref ⟨0, Nat.zero_lt_succ j.val⟩) v))
        j (Fin.tail pref) x) i

#print axioms alphaRoundPartial

/-- The actual transcript prefix, excluding the round's own challenge. -/
def alphaRoundPrefix {n : Nat} (α : Fin n → K) (i : Fin n) : Fin i.val → K :=
  fun j => α (Fin.castLE i.isLt.le j)

#print axioms alphaRoundPrefix

/-- One exact disjunct of `badAlpha`, retaining its existential honest
polynomial and every degree, evaluation and nonzero-difference condition. -/
def alphaRound (d n : Nat) (G : (Fin n → K) → K)
    (polys : Fin n → K[X]) (i : Fin n) (pref : Fin i.val → K) (x : K) : Prop :=
  ∃ h : K[X], h.natDegree ≤ d ∧
    (∀ y, h.eval y = alphaRoundPartial n G i pref y) ∧
    polys i ≠ h ∧ (polys i - h).eval x = 0

#print axioms alphaRound

theorem alphaRound_zero (d n : Nat) (G : (Fin (n+1) → K) → K)
    (polys : Fin (n+1) → K[X]) (α : Fin (n+1) → K) :
    alphaRound d (n+1) G polys 0 (alphaRoundPrefix α 0) (α 0) ↔
      ∃ h : K[X], h.natDegree ≤ d ∧
        (∀ x, h.eval x = bsum n (fun v => G (Fin.cons x v))) ∧
        polys 0 ≠ h ∧ (polys 0 - h).eval (α 0) = 0 := by
  rfl

#print axioms alphaRound_zero

theorem alphaRound_succ (d n : Nat) (G : (Fin (n+1) → K) → K)
    (polys : Fin (n+1) → K[X]) (α : Fin (n+1) → K) (i : Fin n) :
    alphaRound d (n+1) G polys i.succ (alphaRoundPrefix α i.succ) (α i.succ) ↔
      alphaRound d n (fun v => G (Fin.cons (α 0) v)) (Fin.tail polys) i
        (alphaRoundPrefix (Fin.tail α) i) ((Fin.tail α) i) := by
  rfl

#print axioms alphaRound_succ

/-- The recursive transcript event is exactly the union of its per-round
disjuncts at the corresponding transcript prefixes and current challenges. -/
theorem badAlpha_iff_exists_round (d : Nat) : ∀ (n : Nat)
    (G : (Fin n → K) → K) (polys : Fin n → K[X]) (α : Fin n → K),
    badAlpha d n G polys α ↔
      ∃ i : Fin n, alphaRound d n G polys i (alphaRoundPrefix α i) (α i) := by
  intro n
  induction n with
  | zero =>
      intro G polys α
      constructor
      · intro h
        exact False.elim h
      · rintro ⟨i, _⟩
        exact i.elim0
  | succ n ih =>
      intro G polys α
      constructor
      · intro h
        rcases h with hhead | htail
        · exact ⟨0, (alphaRound_zero d n G polys α).mpr hhead⟩
        · obtain ⟨i, hi⟩ :=
            (ih (fun v => G (Fin.cons (α 0) v)) (Fin.tail polys) (Fin.tail α)).mp htail
          exact ⟨i.succ, (alphaRound_succ d n G polys α i).mpr hi⟩
      · rintro ⟨i, hi⟩
        refine Fin.cases ?_ ?_ i hi
        · intro hhead
          exact Or.inl ((alphaRound_zero d n G polys α).mp hhead)
        · intro j htail
          exact Or.inr
            ((ih (fun v => G (Fin.cons (α 0) v)) (Fin.tail polys) (Fin.tail α)).mpr
              ⟨j, (alphaRound_succ d n G polys α j).mp htail⟩)

#print axioms badAlpha_iff_exists_round

noncomputable section
open Classical

/-- The literal round event has at most `d` roots when the prover's round
polynomial also has degree at most `d`. Honest witnesses need not be unique:
their evaluations agree with the same partial-sum function. -/
theorem alphaRound_card [Fintype K] (d n : Nat) (G : (Fin n → K) → K)
    (polys : Fin n → K[X]) (i : Fin n) (pref : Fin i.val → K)
    (hpd : (polys i).natDegree ≤ d) :
    (Finset.univ.filter (alphaRound d n G polys i pref)).card ≤ d := by
  classical
  by_cases hex : ∃ x, alphaRound d n G polys i pref x
  · obtain ⟨_x₀, h₀, hd₀, heval₀, hne₀, _hroot₀⟩ := hex
    have hnonzero : polys i - h₀ ≠ 0 := sub_ne_zero.mpr hne₀
    have hdegree : (polys i - h₀).natDegree ≤ d :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le hpd hd₀)
    have hsub : Finset.univ.filter (alphaRound d n G polys i pref) ⊆
        Finset.univ.filter (fun x : K => (polys i - h₀).eval x = 0) := by
      intro x hx
      obtain ⟨h, _hd, heval, _hne, hroot⟩ := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
      have heq : h.eval x = h₀.eval x := (heval x).trans (heval₀ x).symm
      simpa only [Polynomial.eval_sub, heq] using hroot
    exact (Finset.card_le_card hsub).trans
      (R0P.SemBadSets.univariate_bad_card (polys i - h₀) hnonzero d hdegree)
  · have hempty : Finset.univ.filter (alphaRound d n G polys i pref) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _hx hx
      exact hex ⟨x, hx⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le d

#print axioms alphaRound_card

end

end R0P.Sumcheck

namespace R0P.Sumcheck
open Polynomial

variable {K : Type} [Field K]

/-- Every polynomial checked by an accepted transcript has the checked
round degree bound. This also applies to polynomials selected by a strategy. -/
theorem accept_polys_degree (d : Nat) : ∀ (n : Nat)
    (G : (Fin n → K) → K) (c : K) (polys : Fin n → K[X]) (α : Fin n → K),
    accept d n G c polys α → ∀ i : Fin n, (polys i).natDegree ≤ d := by
  intro n
  induction n with
  | zero =>
      intro G c polys α _hacc i
      exact i.elim0
  | succ n ih =>
      intro G c polys α hacc i
      obtain ⟨hhead, _hsum, htail⟩ := hacc
      refine Fin.cases ?_ ?_ i
      · exact hhead
      · intro j
        exact ih (fun v => G (Fin.cons (α 0) v)) ((polys 0).eval (α 0))
          (Fin.tail polys) (Fin.tail α) htail j

#print axioms accept_polys_degree

/-- An adaptive accepted false claim supplies one of the literal transcript
round events. No converse between these two events is asserted. -/
theorem badAlphaStrategy_imp_exists_round (d n : Nat)
    (G : (Fin n → K) → K) (c : K)
    (strat : (i : Fin n) → (Fin i.val → K) → K[X]) (α : Fin n → K)
    (hdeg : IndDeg d n G)
    (hbad : R0P.SemBadSets.badAlphaStrategy d n G c strat α) :
    ∃ i : Fin n, alphaRound d n G (R0P.SemBadSets.strategyPolys strat α) i
      (alphaRoundPrefix α i) (α i) := by
  apply (badAlpha_iff_exists_round d n G (R0P.SemBadSets.strategyPolys strat α) α).mp
  exact sound d n G c (R0P.SemBadSets.strategyPolys strat α) α hdeg hbad.1 hbad.2

#print axioms badAlphaStrategy_imp_exists_round

end R0P.Sumcheck

namespace R0P
open Polynomial

variable {K : Type} [Field K]

noncomputable section

local instance : DecidableEq K := Classical.decEq K
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The λ-round branch of the fixed LogUp bad event. -/
def lambdaRoundBad (pub : Public K) (t : Trace K) (lam : K) : Prop :=
  prodPolys pub t ≠ consPolys pub t ∧
    (productDifference pub t).leadingCoeff.eval lam = 0

/-- The χ-round branches of the fixed LogUp bad event. -/
def chiRoundBad (pub : Public K) (t : Trace K) (lam chi : K) : Prop :=
  chi = 0 ∨ chi ∈ poleSet t lam ∨
    (numer (valueSet pub t lam) (signedCount pub t lam) ≠ 0 ∧
      (numer (valueSet pub t lam) (signedCount pub t lam)).eval chi = 0)

#print axioms lambdaRoundBad
#print axioms chiRoundBad

theorem badLogUp_rounds_iff (pub : Public K) (t : Trace K) (lam chi : K) :
    BadLogUp pub t lam chi ↔ chiRoundBad pub t lam chi ∨ lambdaRoundBad pub t lam := by
  simp only [BadLogUp, chiRoundBad, lambdaRoundBad, or_assoc]

#print axioms badLogUp_rounds_iff

private noncomputable def roundRootProduct (S : Multiset (K[X])) : (K[X])[X] :=
  (S.map (fun q => (X : Polynomial (K[X])) - C q)).prod

#print axioms roundRootProduct

private theorem roundRootProduct_coeff_degree (S : Multiset (K[X]))
    (hS : ∀ q ∈ S, q.natDegree ≤ 16) (j : Nat) :
    ((roundRootProduct S).coeff j).natDegree ≤ 16 * S.card := by
  classical
  induction S using Multiset.induction_on generalizing j with
  | empty =>
      by_cases hj : j = 0
      · subst j
        simp [roundRootProduct]
      · simp [roundRootProduct, Polynomial.coeff_one, hj]
  | cons q S ih =>
      have hq : q.natDegree ≤ 16 := hS q (by simp)
      have hS' : ∀ x ∈ S, x.natDegree ≤ 16 := by
        intro x hx
        exact hS x (by simp [hx])
      by_cases hj : j = 0
      · subst j
        have hb := ih hS' 0
        simp only [roundRootProduct, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
        change ((((X : Polynomial (K[X])) - C q) * roundRootProduct S).coeff 0).natDegree ≤
          16 * (S.card + 1)
        rw [Polynomial.mul_coeff_zero]
        have hcoeff0 : ((X : Polynomial (K[X])) - C q).coeff 0 = -q := by simp
        rw [hcoeff0]
        calc
          _ ≤ (-q).natDegree + ((roundRootProduct S).coeff 0).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 16 + 16 * S.card := Nat.add_le_add (by simpa using hq) hb
          _ = 16 * (S.card + 1) := by omega
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        have hb := ih hS' k
        have hb' := ih hS' (k + 1)
        simp only [roundRootProduct, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
        change ((((X : Polynomial (K[X])) - C q) * roundRootProduct S).coeff (k + 1)).natDegree ≤
          16 * (S.card + 1)
        rw [Polynomial.coeff_X_sub_C_mul]
        have hmul : (q * (roundRootProduct S).coeff (k + 1)).natDegree ≤
            16 + 16 * S.card := by
          calc
            _ ≤ q.natDegree + ((roundRootProduct S).coeff (k + 1)).natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ 16 + 16 * S.card := Nat.add_le_add hq hb'
        calc
          _ ≤ max ((roundRootProduct S).coeff k).natDegree
              (q * (roundRootProduct S).coeff (k + 1)).natDegree := Polynomial.natDegree_sub_le _ _
          _ ≤ 16 * (S.card + 1) := by omega

#print axioms roundRootProduct_coeff_degree

private theorem round_poly_degree_le_16 (pub : Public K) (t : Trace K)
    (hprod : ∀ q ∈ prodPolys pub t, q.natDegree ≤ 16)
    (hcons : ∀ q ∈ consPolys pub t, q.natDegree ≤ 16) :
    (productDifference pub t).leadingCoeff.natDegree ≤
      16 * max (prodPolys pub t).card (consPolys pub t).card := by
  let S := prodPolys pub t
  let T := consPolys pub t
  have hS : ∀ q ∈ S, q.natDegree ≤ 16 := hprod
  have hT : ∀ q ∈ T, q.natDegree ≤ 16 := hcons
  have hcoeffS := roundRootProduct_coeff_degree S hS (productDifference pub t).natDegree
  have hcoeffT := roundRootProduct_coeff_degree T hT (productDifference pub t).natDegree
  change ((roundRootProduct S - roundRootProduct T).coeff
    (roundRootProduct S - roundRootProduct T).natDegree).natDegree ≤ _
  rw [Polynomial.coeff_sub]
  calc
    _ ≤ max ((roundRootProduct S).coeff (productDifference pub t).natDegree).natDegree
        ((roundRootProduct T).coeff (productDifference pub t).natDegree).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ max (16 * S.card) (16 * T.card) :=
      max_le (hcoeffS.trans (le_max_left _ _)) (hcoeffT.trans (le_max_right _ _))
    _ = 16 * max S.card T.card := by
      rcases le_total S.card T.card with h | h
      · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_left 16 h)]
      · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul_left 16 h)]

#print axioms round_poly_degree_le_16

private theorem round_enabled_card_le (pub : Public K) :
    (enabledLinks pub).length ≤ 136 := by
  simpa only [enabledLinks] using copy_enabled_endpoints_le pub

#print axioms round_enabled_card_le

private theorem round_poly_multiset_card_le_136 (pub : Public K) (t : Trace K) :
    (prodPolys pub t).card ≤ 136 ∧ (consPolys pub t).card ≤ 136 := by
  have h := round_enabled_card_le pub
  constructor
  · calc
      _ = (enabledLinks pub).length := by simp [prodPolys]
      _ ≤ 136 := h
  · calc
      _ = (enabledLinks pub).length := by simp [consPolys]
      _ ≤ 136 := h

#print axioms round_poly_multiset_card_le_136

private theorem round_compress_degree (tuple : K × (Fin 16 → K)) :
    (compressPoly tuple).natDegree ≤ 16 := by
  have hz : compressPoly ((0 : K), fun _ : Fin 16 => 0) = 0 := by
    simp only [compressPoly, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simpa only [hz, sub_zero] using
    compressPoly_sub_natDegree_le tuple ((0 : K), fun _ : Fin 16 => 0)

#print axioms round_compress_degree

theorem lambdaRoundBad_card [Fintype K] (pub : Public K) (t : Trace K) :
    (Finset.univ.filter (lambdaRoundBad pub t)).card ≤ 2176 := by
  classical
  by_cases hneq : prodPolys pub t ≠ consPolys pub t
  · have hprod : ∀ q ∈ prodPolys pub t, q.natDegree ≤ 16 := by
      intro q hq
      change q ∈ (enabledLinks pub).map (fun l => compressPoly (copyProducerTuple t l)) at hq
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hq
      exact round_compress_degree _
    have hcons : ∀ q ∈ consPolys pub t, q.natDegree ≤ 16 := by
      intro q hq
      change q ∈ (enabledLinks pub).map (fun l => compressPoly (copyConsumerTuple t l)) at hq
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hq
      exact round_compress_degree _
    have hrootdiff := SemBadSets.product_difference_coeff
      (prodPolys pub t) (consPolys pub t) hneq hprod hcons
    have hdiff : productDifference pub t ≠ 0 := by
      apply sub_ne_zero.mpr
      exact hrootdiff.1
    have hlead : (productDifference pub t).leadingCoeff ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hdiff
    have hdegree := round_poly_degree_le_16 pub t hprod hcons
    have hcards := round_poly_multiset_card_le_136 pub t
    have hdegree' : (productDifference pub t).leadingCoeff.natDegree ≤ 2176 := by
      have hm : max (prodPolys pub t).card (consPolys pub t).card ≤ 136 :=
        max_le hcards.1 hcards.2
      have hscale := Nat.mul_le_mul_left 16 hm
      norm_num at hscale ⊢
      exact hdegree.trans hscale
    have hinc : (Finset.univ.filter (lambdaRoundBad pub t)) ⊆
        Finset.univ.filter (fun lam : K => (productDifference pub t).leadingCoeff.eval lam = 0) := by
      intro lam hlam
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hlam).2.2⟩
    calc
      _ ≤ (Finset.univ.filter (fun lam : K =>
          (productDifference pub t).leadingCoeff.eval lam = 0)).card := Finset.card_le_card hinc
      _ ≤ 2176 := SemBadSets.univariate_bad_card _ hlead 2176 hdegree'
  · have hempty : Finset.univ.filter (lambdaRoundBad pub t) = ∅ := by
      ext lam
      simp [lambdaRoundBad, hneq]
    rw [hempty]
    simp

#print axioms lambdaRoundBad_card

private theorem round_copy_links_length : copyLinks.length = 136 := by
  have h := congrArg List.length copy_tags_indexed
  simpa using h

#print axioms round_copy_links_length

private theorem round_pole_set_card_le_272 (t : Trace K) (lam : K) :
    (poleSet t lam).card ≤ 272 := by
  unfold poleSet
  calc
    _ ≤ (copyLinks.map (prodVal t lam) ++ copyLinks.map (consVal t lam)).length :=
      List.toFinset_card_le _
    _ = copyLinks.length + copyLinks.length := by simp
    _ = 272 := by rw [round_copy_links_length]

#print axioms round_pole_set_card_le_272

private theorem round_value_set_card_le_272 (pub : Public K) (t : Trace K) (lam : K) :
    (valueSet pub t lam).card ≤ 272 := by
  unfold valueSet
  calc
    _ ≤ ((enabledLinks pub).map (prodVal t lam) ++
        (enabledLinks pub).map (consVal t lam)).length := List.toFinset_card_le _
    _ = (enabledLinks pub).length + (enabledLinks pub).length := by simp
    _ ≤ 272 := by have h := round_enabled_card_le pub; omega

#print axioms round_value_set_card_le_272

theorem chiRoundBad_card [Fintype K] (pub : Public K) (t : Trace K) (lam : K) :
    (Finset.univ.filter (chiRoundBad pub t lam)).card ≤ 544 := by
  classical
  let D := valueSet pub t lam
  let m := signedCount pub t lam
  let N := numer D m
  let R := N.roots.toFinset
  let target : Finset K := ({0} ∪ poleSet t lam) ∪ R
  have hroot : R.card ≤ 271 := by
    by_cases hN : N = 0
    · simp [R, N, hN]
    · have hb := numer_nonzero_bounds D m hN
      have hcard : R.card ≤ N.roots.card := Multiset.toFinset_card_le N.roots
      have hsize : D.card ≤ 272 := by exact round_value_set_card_le_272 pub t lam
      have hroots : N.roots.card ≤ D.card - 1 := hb.2
      have hroots' : N.roots.card ≤ 271 := by omega
      exact hcard.trans hroots'
  have hpole : (poleSet t lam).card ≤ 272 := round_pole_set_card_le_272 t lam
  have hsubset : (Finset.univ.filter (chiRoundBad pub t lam)) ⊆ target := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    rcases hx' with hzero | hpole | hnum
    · simp only [target, Finset.mem_union, Finset.mem_singleton]
      exact Or.inl (Or.inl hzero)
    · simp only [target, Finset.mem_union]
      exact Or.inl (Or.inr hpole)
    · have hr : x ∈ R := by
        change x ∈ N.roots.toFinset
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hnum.1]
        exact hnum.2
      exact Finset.mem_union.mpr (Or.inr hr)
  have htarget : target.card ≤ 544 := by
    calc
      _ ≤ ({0} : Finset K).card + (poleSet t lam).card + R.card := by
        calc
          _ ≤ ({0} ∪ poleSet t lam).card + R.card :=
            Finset.card_union_le ({0} ∪ poleSet t lam) R
          _ ≤ ({0} : Finset K).card + (poleSet t lam).card + R.card :=
            Nat.add_le_add_right
              (Finset.card_union_le ({0} : Finset K) (poleSet t lam)) R.card
      _ ≤ 1 + 272 + 271 := by
        simp only [Finset.card_singleton]
        omega
      _ = 544 := by norm_num
  exact (Finset.card_le_card hsubset).trans htarget

#print axioms chiRoundBad_card

end

end R0P

noncomputable section

namespace R0P.SemRounds

open R0P.Sumcheck

variable {K : Type} [Field K]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Collapse the first challenge coordinate of a Boolean function by multilinear
interpolation, leaving a function on the Boolean tail. -/
def mleRestrict (n : Nat) (f : (Fin (n + 1) → Bool) → K) (x : K) :
    (Fin n → Bool) → K :=
  fun b => (1 - x) * f (Fin.cons false b) + x * f (Fin.cons true b)

/-- The finite Boolean vector consisting of the coordinates before `i`. -/
def zcPrefix {n : Nat} (z : Fin n → K) (i : Fin n) : Fin i.val → K :=
  fun j => z ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

/-- The first coordinate at which partial interpolation of a nonzero Boolean
function becomes the zero function. -/
def zcRound : (n : Nat) → ((Fin n → Bool) → K) →
    (i : Fin n) → (Fin i.val → K) → K → Prop
  | 0, _, i => i.elim0
  | n + 1, f, i =>
      Fin.cases
        (fun _ x => f ≠ 0 ∧ mleRestrict n f x = 0)
        (fun j pref x =>
          zcRound n (mleRestrict n f (pref ⟨0, Nat.zero_lt_succ j.val⟩))
            j (Fin.tail pref) x)
        i

#print axioms mleRestrict
#print axioms zcPrefix
#print axioms zcRound

theorem mle_smul (n : Nat) (a : K) (f : (Fin n → Bool) → K) (z : Fin n → K) :
    mle n (fun b => a * f b) z = a * mle n f z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [mle]
      rw [ih, ih]
      ring

#print axioms mle_smul

theorem mle_add (n : Nat) (f g : (Fin n → Bool) → K) (z : Fin n → K) :
    mle n (fun b => f b + g b) z = mle n f z + mle n g z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [mle]
      rw [ih, ih]
      ring

#print axioms mle_add

theorem mle_restrict (n : Nat) (f : (Fin (n + 1) → Bool) → K) (x : K)
    (z : Fin n → K) :
    mle n (mleRestrict n f x) z =
      (1 - x) * mle n (fun b => f (Fin.cons false b)) z +
        x * mle n (fun b => f (Fin.cons true b)) z := by
  change mle n (fun b => (1 - x) * f (Fin.cons false b) +
    x * f (Fin.cons true b)) z = _
  rw [mle_add, mle_smul, mle_smul]

#print axioms mle_restrict

theorem mle_cons_restrict (n : Nat) (f : (Fin (n + 1) → Bool) → K)
    (x : K) (z : Fin n → K) :
    mle (n + 1) f (Fin.cons x z) = mle n (mleRestrict n f x) z := by
  simp only [mle]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [mle_restrict]

#print axioms mle_cons_restrict

omit [Field K] in
theorem zcPrefix_succ {n : Nat} (z : Fin (n + 1) → K) (i : Fin n) :
    zcPrefix z i.succ = Fin.cons (z 0) (zcPrefix (Fin.tail z) i) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [zcPrefix]
  · intro j
    change z ⟨j.val + 1, _⟩ = z (Fin.succ ⟨j.val, _⟩)
    congr 1

#print axioms zcPrefix_succ

theorem zcRound_succ (n : Nat) (f : (Fin (n + 1) → Bool) → K) (i : Fin n)
    (pref : Fin (i.val + 1) → K) (x : K) :
    zcRound (n + 1) f i.succ pref x =
    zcRound n (mleRestrict n f (pref ⟨0, Nat.zero_lt_succ i.val⟩)) i (Fin.tail pref) x := by
  rfl

#print axioms zcRound_succ

theorem zcRound_exists_split (n : Nat) (f : (Fin (n + 1) → Bool) → K)
    (z : Fin (n + 1) → K) :
    (∃ i : Fin (n + 1), zcRound (n + 1) f i (zcPrefix z i) (z i)) ↔
      (f ≠ 0 ∧ mleRestrict n f (z 0) = 0) ∨
        (∃ i : Fin n,
          zcRound n (mleRestrict n f (z 0)) i (zcPrefix (Fin.tail z) i)
            (Fin.tail z i)) := by
  constructor
  · rintro ⟨i, hi⟩
    rcases Fin.eq_zero_or_eq_succ i with hzero | ⟨j, rfl⟩
    · subst i
      left
      simpa [zcRound, zcPrefix] using hi
    · right
      rw [zcRound_succ, zcPrefix_succ] at hi
      exact ⟨j, hi⟩
  · rintro (⟨hf, hzero⟩ | ⟨i, hi⟩)
    · refine ⟨0, ?_⟩
      simpa [zcRound, zcPrefix] using And.intro hf hzero
    · refine ⟨i.succ, ?_⟩
      rw [zcRound_succ, zcPrefix_succ]
      exact hi

#print axioms zcRound_exists_split

theorem mle_zero_of_fun_eq_zero (n : Nat) (z : Fin n → K)
    (f : (Fin n → Bool) → K) (hf : f = 0) : mle n f z = 0 := by
  subst f
  induction n with
  | zero => rfl
  | succ n ih =>
      change (1 - z 0) * mle n (0 : (Fin n → Bool) → K) (Fin.tail z) +
        z 0 * mle n (0 : (Fin n → Bool) → K) (Fin.tail z) = 0
      rw [ih]
      ring

#print axioms mle_zero_of_fun_eq_zero

/-- The roundwise collapse event identifies precisely the nonzero Boolean
functions whose multilinear extension vanishes at the challenge point. -/
theorem zc_rounds_iff (n : Nat) (f : (Fin n → Bool) → K) (z : Fin n → K) :
    (f ≠ 0 ∧ mle n f z = 0) ↔
      ∃ i : Fin n, zcRound n f i (zcPrefix z i) (z i) := by
  induction n with
  | zero =>
      constructor
      · rintro ⟨hf, hz⟩
        have hzero : f = 0 := by
          funext b
          have hb : b = (fun i : Fin 0 => i.elim0) := by
            funext i
            exact Fin.elim0 i
          rw [hb]
          change f (fun i : Fin 0 => i.elim0) = 0 at hz
          exact hz
        exact (hf hzero).elim
      · rintro ⟨i, hi⟩
        exact Fin.elim0 i
  | succ n ih =>
      let x := z 0
      let tail := Fin.tail z
      let g := mleRestrict n f x
      have hz : z = Fin.cons x tail := by
        exact (Fin.cons_self_tail z).symm
      rw [hz]
      rw [mle_cons_restrict]
      rw [zcRound_exists_split]
      simp only [Fin.cons_zero, Fin.tail_cons]
      constructor
      · rintro ⟨hf, hzero⟩
        by_cases hg : g = 0
        · exact Or.inl ⟨hf, by
            change g = 0
            exact hg⟩
        · exact Or.inr ((ih g tail).1 ⟨hg, by simpa [g, x, tail] using hzero⟩)
      · rintro (⟨hf, hg⟩ | htail)
        · refine ⟨hf, ?_⟩
          simpa [g, x] using (mle_zero_of_fun_eq_zero n tail g hg)
        · obtain ⟨hg, hzero⟩ := (ih g tail).2 htail
          have hf : f ≠ 0 := by
            intro h
            have : g = 0 := by
              change mleRestrict n f x = 0
              rw [h]
              funext b
              change (1 - x) * 0 + x * 0 = 0
              ring
            exact hg this
          exact ⟨hf, by simpa [g, x, tail] using hzero⟩

#print axioms zc_rounds_iff

/-- At a fixed Boolean witness where `f` is nonzero, at most one challenge
can collapse the entire Boolean tail function to zero. -/
theorem zc_head_roots_card [Fintype K] {n : Nat}
    (f : (Fin (n + 1) → Bool) → K) (b : Fin (n + 1) → Bool) (hb : f b ≠ 0) :
    (Finset.univ.filter (fun x : K => mleRestrict n f x = 0)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro x y hx hy
  let t := Fin.tail b
  let a := f (Fin.cons false t)
  let c := f (Fin.cons true t)
  have hbcons : b = Fin.cons (b 0) t := by
    change b = Fin.cons (b 0) (Fin.tail b)
    exact (Fin.cons_self_tail b).symm
  have ha_or_hc : a ≠ 0 ∨ c ≠ 0 := by
    have hb' : f (Fin.cons (b 0) t) ≠ 0 := by rw [← hbcons]; exact hb
    by_cases hbit : b 0
    · right
      simpa [c, t, hbit] using hb'
    · left
      simpa [a, t, hbit] using hb'
  have hxeq : (1 - x) * a + x * c = 0 := by
    have h := congrFun (Finset.mem_filter.mp hx).2 t
    simpa [mleRestrict, a, c, t] using h
  have hyeq : (1 - y) * a + y * c = 0 := by
    have h := congrFun (Finset.mem_filter.mp hy).2 t
    simpa [mleRestrict, a, c, t] using h
  have hx' : a + x * (c - a) = 0 := by linear_combination hxeq
  have hy' : a + y * (c - a) = 0 := by linear_combination hyeq
  have hprod : (x - y) * (c - a) = 0 := by linear_combination hx' - hy'
  have hca : c - a ≠ 0 := by
    intro hzero
    have hca' : c = a := sub_eq_zero.mp hzero
    rcases ha_or_hc with ha | hc
    · rw [hca'] at hxeq
      have ha0 : a = 0 := by linear_combination hxeq
      exact ha ha0
    · rw [hca'] at hc
      rw [hca'] at hxeq
      have hc0 : a = 0 := by linear_combination hxeq
      exact hc hc0
  rcases mul_eq_zero.mp hprod with hxy | hxy
  · exact sub_eq_zero.mp hxy
  · exact (hca hxy).elim

#print axioms zc_head_roots_card

/-- For any fixed coordinate and already-chosen prefix, the next challenge
values causing a zero collapse form a set of size at most one. -/
theorem zcRound_card [Fintype K] : ∀ (n : Nat)
    (f : (Fin n → Bool) → K) (i : Fin n) (pref : Fin i.val → K),
    (Finset.univ.filter (fun x : K => zcRound n f i pref x)).card ≤ 1 := by
  classical
  intro n
  induction n with
  | zero =>
      intro f i
      exact Fin.elim0 i
  | succ n ih =>
      intro f i pref
      rcases Fin.eq_zero_or_eq_succ i with hzero | ⟨j, rfl⟩
      · subst i
        by_cases hf : f = 0
        · have hfilter :
              Finset.univ.filter (fun x : K => zcRound (n + 1) f 0 pref x) = ∅ := by
            ext x
            simp [zcRound, hf]
          simp [hfilter]
        · obtain ⟨b, hb⟩ : ∃ b : Fin (n + 1) → Bool, f b ≠ 0 := by
            by_contra h
            have hz : ∀ b : Fin (n + 1) → Bool, f b = 0 := by
              intro b
              by_contra hfb
              exact h ⟨b, hfb⟩
            apply hf
            funext b
            exact hz b
          have hsubset :
              Finset.univ.filter (fun x : K => zcRound (n + 1) f 0 pref x) ⊆
                Finset.univ.filter (fun x : K => mleRestrict n f x = 0) := by
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            have he : f ≠ 0 ∧ mleRestrict n f x = 0 := by
              exact hx
            exact he.2
          exact (Finset.card_le_card hsubset).trans (zc_head_roots_card f b hb)
      · let pref' : Fin (j.val + 1) → K := pref
        simpa only [zcRound_succ] using
          ih (mleRestrict n f (pref' ⟨0, Nat.zero_lt_succ j.val⟩)) j (Fin.tail pref')

#print axioms zcRound_card

end R0P.SemRounds
end

noncomputable section
namespace R0P
open Polynomial Sumcheck SemRounds
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- Total lookup for an earlier-challenge prefix. Every lookup used by a
round is strictly before that round; the other entries are unused padding. -/
def semPrefixVal {n : Nat} (pref : Fin n → K) (k : Nat) : K :=
  if h : k < n then pref ⟨k, h⟩ else 0

/-- A consecutive coordinate slice of a challenge prefix. -/
def semSlice {n : Nat} (pref : Fin n → K) (start len : Nat) : Fin len → K :=
  fun j => semPrefixVal pref (start + j.val)

/-- Challenges strictly earlier than the specified semantic round. -/
def semPrefix (r : Fin 24 → K) (i : Fin 24) : Fin i.val → K :=
  fun j => r (Fin.castLE i.isLt.le j)

/-- The source's per-candidate budgets, in the 24-round challenge order. -/
def semRoundBudget (i : Fin 24) : Nat :=
  if i.val = 0 then 2176 else if i.val = 1 then 544 else
  if i.val = 2 then 28 else if i.val < 13 then 1 else
  if i.val = 13 then 2 else 27

/-- The degree check already performed before an alpha challenge is drawn.
This is a premise of the counting theorem only. -/
def semRoundDegreeChecked
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (i : Fin 24) (pref : Fin i.val → K) : Prop :=
  if h : 14 ≤ i.val then
    let j : Fin 10 := ⟨i.val - 14, by omega⟩
    (strat (semSlice pref 0 14) j (semSlice pref 14 j.val)).natDegree ≤ 27
  else True

/-- The exact semantic-round events. The virtual polynomial is fixed by the
first fourteen challenges; the adaptive prover polynomial sees only earlier
alpha challenges. The current challenge is supplied separately. -/
def semRoundBad {F : Subfield K} (t : Trace K) (pub : Public K) (B : PackBasis F)
    (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (i : Fin 24) (pref : Fin i.val → K) (x : K) : Prop :=
  if h0 : i.val = 0 then lambdaRoundBad pub t x else
  if h1 : i.val = 1 then chiRoundBad pub t (semPrefixVal pref 0) x else
  if h2 : i.val = 2 then
    BadTheta (laneOf t pub (semPrefixVal pref 0) (semPrefixVal pref 1) B) x else
  if hz : i.val < 13 then
    let j : Fin 10 := ⟨i.val - 3, by omega⟩
    zcRound 10
      (lanesComp (semPrefixVal pref 2)
        (laneOf t pub (semPrefixVal pref 0) (semPrefixVal pref 1) B))
      j (semSlice pref 3 j.val) x else
  if hm : i.val = 13 then
    BadMu
      (mle 10 (lanesComp (semPrefixVal pref 2)
        (laneOf t pub (semPrefixVal pref 0) (semPrefixVal pref 1) B)) (semSlice pref 3 10))
      (bsumB 10 (fun b => t 26 (rowOf b)))
      (bsumB 10 (fun b =>
        (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))) x else
    let j : Fin 10 := ⟨i.val - 14, by omega⟩
    let pref14 := semSlice pref 0 14
    let apref := semSlice pref 14 j.val
    alphaRound 27 10 (G pref14) (fun _ => strat pref14 j apref) j apref x

#print axioms semPrefixVal
#print axioms semSlice
#print axioms semPrefix
#print axioms semRoundBudget
#print axioms semRoundDegreeChecked
#print axioms semRoundBad

/-- Per-candidate root counts with the source's pre-challenge degree check
used only for the alpha counting case. -/
theorem semRoundBad_card [Fintype K] {F : Subfield K}
    (t : Trace K) (pub : Public K) (B : PackBasis F)
    (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (i : Fin 24) (pref : Fin i.val → K)
    (hchecked : semRoundDegreeChecked strat i pref) :
    (Finset.univ.filter (semRoundBad t pub B G strat i pref)).card ≤ semRoundBudget i := by
  unfold semRoundBad semRoundBudget
  split_ifs with h0 h1 h2 hz hm
  · exact lambdaRoundBad_card pub t
  · exact chiRoundBad_card pub t (semPrefixVal pref 0)
  · exact SemBadSets.badTheta_card _
  · exact zcRound_card 10 _ _ _
  · exact SemBadSets.badMu_card _ _ _
  · have hi : 14 ≤ i.val := by omega
    have hp := hchecked
    simp only [semRoundDegreeChecked, dif_pos hi] at hp
    exact alphaRound_card 27 10 _ _ _ _ hp

#print axioms semRoundBad_card

end R0P
end

namespace R0P
open Polynomial Sumcheck SemRounds

variable {K : Type} [Field K]

private theorem semPrefixVal_actual (r : Fin 24 → K) (i : Fin 24)
    (k : Nat) (hk : k < i.val) :
    semPrefixVal (semPrefix r i) k = r ⟨k, hk.trans i.isLt⟩ := by
  simp only [semPrefixVal, dif_pos hk, semPrefix]
  rfl

#print axioms semPrefixVal_actual

private theorem semSlice_actual (r : Fin 24 → K) (start len : Nat)
    (hbound : start + len ≤ 24) (j : Fin len) :
    semSlice r start len j = r ⟨start + j.val, by omega⟩ := by
  have hj : start + j.val < 24 := by omega
  simp only [semSlice, semPrefixVal, dif_pos hj]

#print axioms semSlice_actual

private theorem semSlice_prefix_actual (r : Fin 24 → K) (i : Fin 24)
    (start len : Nat) (hbound : start + len ≤ i.val) :
    semSlice (semPrefix r i) start len = semSlice r start len := by
  funext j
  have hj : start + j.val < i.val := by omega
  have hj24 : start + j.val < 24 := hj.trans i.isLt
  simp only [semSlice, semPrefixVal, dif_pos hj, dif_pos hj24, semPrefix]
  rfl

#print axioms semSlice_prefix_actual

private theorem semRoundBad_zero {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (x : K) :
    semRoundBad t pub B G strat 0 (semPrefix r 0) x ↔ lambdaRoundBad pub t x := by
  simp [semRoundBad]

#print axioms semRoundBad_zero

private theorem semRoundBad_one {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (x : K) :
    semRoundBad t pub B G strat 1 (semPrefix r 1) x ↔ chiRoundBad pub t (r 0) x := by
  simp [semRoundBad, semPrefixVal, semPrefix]

#print axioms semRoundBad_one

private theorem semRoundBad_two {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (x : K) :
    semRoundBad t pub B G strat 2 (semPrefix r 2) x ↔
      BadTheta (laneOf t pub (r 0) (r 1) B) x := by
  simp [semRoundBad, semPrefixVal, semPrefix]

#print axioms semRoundBad_two

private theorem semRoundBad_zc {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (j : Fin 10) (x : K) :
    semRoundBad t pub B G strat ⟨3 + j.val, by omega⟩
        (semPrefix r ⟨3 + j.val, by omega⟩) x ↔
      zcRound 10 (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B))
        j (zcPrefix (semSlice r 3 10) j) x := by
  let i : Fin 24 := ⟨3 + j.val, by omega⟩
  change semRoundBad t pub B G strat i (semPrefix r i) x ↔ _
  have h0 : i.val ≠ 0 := by dsimp [i]; omega
  have h1 : i.val ≠ 1 := by dsimp [i]; omega
  have h2 : i.val ≠ 2 := by dsimp [i]; omega
  have hz : i.val < 13 := by dsimp [i]; omega
  have hj : (⟨i.val - 3, by dsimp [i]; omega⟩ : Fin 10) = j := by
    apply Fin.ext
    dsimp [i]
    omega
  have hp0 : semPrefixVal (semPrefix r i) 0 = r 0 :=
    semPrefixVal_actual r i 0 (by dsimp [i]; omega)
  have hp1 : semPrefixVal (semPrefix r i) 1 = r 1 :=
    semPrefixVal_actual r i 1 (by dsimp [i]; omega)
  have hp2 : semPrefixVal (semPrefix r i) 2 = r 2 :=
    semPrefixVal_actual r i 2 (by dsimp [i]; omega)
  have hslice : semSlice (semPrefix r i) 3 j.val = zcPrefix (semSlice r 3 10) j := by
    rw [semSlice_prefix_actual r i 3 j.val (by dsimp [i]; omega)]
    rfl
  simp only [semRoundBad, dif_neg h0, dif_neg h1, dif_neg h2, dif_pos hz,
    hp0, hp1, hp2]
  have hview := congrArg (fun k : Fin 10 =>
    zcRound 10 (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B))
      k (semSlice (semPrefix r i) 3 k.val) x) hj
  rw [hslice] at hview
  exact Iff.of_eq hview

#print axioms semRoundBad_zc

private theorem semRoundBad_mu {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (x : K) :
    semRoundBad t pub B G strat 13 (semPrefix r 13) x ↔
      BadMu
        (mle 10 (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B)) (semSlice r 3 10))
        (bsumB 10 (fun b => t 26 (rowOf b)))
        (bsumB 10 (fun b =>
          (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))) x := by
  have h0 : (13 : Fin 24).val ≠ 0 := by decide
  have h1 : (13 : Fin 24).val ≠ 1 := by decide
  have h2 : (13 : Fin 24).val ≠ 2 := by decide
  have hz : ¬ (13 : Fin 24).val < 13 := by decide
  have hm : (13 : Fin 24).val = 13 := rfl
  have hp0 : semPrefixVal (semPrefix r 13) 0 = r 0 :=
    semPrefixVal_actual r 13 0 (by decide)
  have hp1 : semPrefixVal (semPrefix r 13) 1 = r 1 :=
    semPrefixVal_actual r 13 1 (by decide)
  have hp2 : semPrefixVal (semPrefix r 13) 2 = r 2 :=
    semPrefixVal_actual r 13 2 (by decide)
  have hslice := semSlice_prefix_actual r 13 3 10 (by decide)
  simp only [semRoundBad, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg hz,
    dif_pos hm, hp0, hp1, hp2, hslice]

#print axioms semRoundBad_mu

private theorem semRoundBad_alpha {F : Subfield K} (t : Trace K) (pub : Public K)
    (B : PackBasis F) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K) (j : Fin 10) (x : K) :
    semRoundBad t pub B G strat ⟨14 + j.val, by omega⟩
        (semPrefix r ⟨14 + j.val, by omega⟩) x ↔
      alphaRound 27 10 (G (semSlice r 0 14))
        (SemBadSets.strategyPolys (strat (semSlice r 0 14)) (semSlice r 14 10))
        j (alphaRoundPrefix (semSlice r 14 10) j) x := by
  let i : Fin 24 := ⟨14 + j.val, by omega⟩
  change semRoundBad t pub B G strat i (semPrefix r i) x ↔ _
  have h0 : i.val ≠ 0 := by dsimp [i]; omega
  have h1 : i.val ≠ 1 := by dsimp [i]; omega
  have h2 : i.val ≠ 2 := by dsimp [i]; omega
  have hz : ¬ i.val < 13 := by dsimp [i]; omega
  have hm : i.val ≠ 13 := by dsimp [i]; omega
  have hj : (⟨i.val - 14, by dsimp [i]; omega⟩ : Fin 10) = j := by
    apply Fin.ext
    dsimp [i]
    omega
  have hpre14 : semSlice (semPrefix r i) 0 14 = semSlice r 0 14 :=
    semSlice_prefix_actual r i 0 14 (by dsimp [i]; omega)
  have hapre : semSlice (semPrefix r i) 14 j.val =
      alphaRoundPrefix (semSlice r 14 10) j := by
    rw [semSlice_prefix_actual r i 14 j.val (by dsimp [i]; omega)]
    rfl
  simp only [semRoundBad, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg hz,
    dif_neg hm, hpre14]
  have hview := congrArg (fun k : Fin 10 =>
    alphaRound 27 10 (G (semSlice r 0 14))
      (fun _ => strat (semSlice r 0 14) k (semSlice (semPrefix r i) 14 k.val))
      k (semSlice (semPrefix r i) 14 k.val) x) hj
  rw [hapre] at hview
  exact Iff.of_eq hview

#print axioms semRoundBad_alpha

/-- Avoiding every source-ordered round event avoids all five bad events
consumed by the closed semantic theorem. -/
theorem semRounds_cover {F : Subfield K} (t : Trace K) (pub : Public K) (B : PackBasis F)
    (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (r : Fin 24 → K)
    (hrounds : ∀ i, ¬ semRoundBad t pub B G strat i (semPrefix r i) (r i)) :
    (¬ BadLogUp pub t (r 0) (r 1)) ∧
    (¬ BadTheta (laneOf t pub (r 0) (r 1) B) (r 2)) ∧
    (¬ BadZc (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B)) (semSlice r 3 10)) ∧
    (¬ BadMu
      (mle 10 (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B)) (semSlice r 3 10))
      (bsumB 10 (fun b => t 26 (rowOf b)))
      (bsumB 10 (fun b =>
        (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b))) (r 13)) ∧
    (¬ BadAlpha 27 10 (G (semSlice r 0 14))
      (SemBadSets.strategyPolys (strat (semSlice r 0 14)) (semSlice r 14 10))
      (semSlice r 14 10)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hbad
    rcases (badLogUp_rounds_iff pub t (r 0) (r 1)).mp hbad with hchi | hlam
    · exact hrounds 1 ((semRoundBad_one t pub B G strat r (r 1)).mpr hchi)
    · exact hrounds 0 ((semRoundBad_zero t pub B G strat r (r 0)).mpr hlam)
  · intro hbad
    exact hrounds 2 ((semRoundBad_two t pub B G strat r (r 2)).mpr hbad)
  · rintro ⟨⟨b, hb⟩, hzero⟩
    have hfun : lanesComp (r 2) (laneOf t pub (r 0) (r 1) B) ≠ 0 := by
      intro heq
      exact hb (congrFun heq b)
    obtain ⟨j, hj⟩ := (zc_rounds_iff 10
      (lanesComp (r 2) (laneOf t pub (r 0) (r 1) B)) (semSlice r 3 10)).mp ⟨hfun, hzero⟩
    rw [semSlice_actual r 3 10 (by decide) j] at hj
    exact hrounds ⟨3 + j.val, by omega⟩
      ((semRoundBad_zc t pub B G strat r j _).mpr hj)
  · intro hbad
    exact hrounds 13 ((semRoundBad_mu t pub B G strat r (r 13)).mpr hbad)
  · intro hbad
    obtain ⟨j, hj⟩ := (badAlpha_iff_exists_round 27 10 (G (semSlice r 0 14))
      (SemBadSets.strategyPolys (strat (semSlice r 0 14)) (semSlice r 14 10))
      (semSlice r 14 10)).mp hbad
    rw [semSlice_actual r 14 10 (by decide) j] at hj
    exact hrounds ⟨14 + j.val, by omega⟩
      ((semRoundBad_alpha t pub B G strat r j _).mpr hj)

#print axioms semRounds_cover

/-- The closed semantic theorem with source-ordered round-event exclusions.
Only the five bad-set hypotheses are supplied through `semRounds_cover`. -/
theorem semantic_sound_rounds (P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1)
    (F : Subfield K) (B : PackBasis F) (pub : Public K) (t : Trace K)
    (hA : BaseTyped F t) (hpub : PublicBase F pub)
    (r : Fin 24 → K) (G : (Fin 14 → K) → (Fin 10 → K) → K)
    (strat : (Fin 14 → K) → (j : Fin 10) → (Fin j.val → K) → K[X])
    (hG : ∀ b, G (semSlice r 0 14) (ofBool b) =
      eqwB 10 (semSlice r 3 10) b * lanesComp (r 2) (laneOf t pub (r 0) (r 1) B) b +
      r 13 * t 26 (rowOf b) +
      (r 13) ^ 2 * ((1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)))
    (hdeg : IndDeg 27 10 (G (semSlice r 0 14)))
    (hacc : accept 27 10 (G (semSlice r 0 14)) 0
      (SemBadSets.strategyPolys (strat (semSlice r 0 14)) (semSlice r 14 10)) (semSlice r 14 10))
    (hrounds : ∀ i, ¬ semRoundBad t pub B G strat i (semPrefix r i) (r i)) :
    ProductionHolds pub (r 0) (r 1) t ∧ CopyLinkBalance pub t := by
  obtain ⟨hlc, htheta, hzc, hmu, halpha⟩ := semRounds_cover t pub B G strat r hrounds
  exact semantic_sound_closed P hP F B pub t hA hpub
    (r 0) (r 1) (r 2) (r 13) (semSlice r 3 10) hlc
    (G (semSlice r 0 14))
    (SemBadSets.strategyPolys (strat (semSlice r 0 14)) (semSlice r 14 10))
    (semSlice r 14 10) hG hdeg hacc halpha hmu hzc htheta

#print axioms semantic_sound_rounds

end R0P
