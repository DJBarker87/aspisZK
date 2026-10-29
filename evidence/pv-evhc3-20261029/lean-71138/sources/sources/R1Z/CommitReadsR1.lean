import R1Z.LazyTable
import R0Z.FsAbortTape

/-! R1 commitment-phase reads: the mask-sampler exhaustion mass (G-exh) and
the commitment-read count Mc (G-count), from the Rust source.

Source (read-only, `git show origin/codex/100bit-spend-path-20261013:…`):
* aspis-prover/src/state_only_hiding.rs `SeedExpander::m31` and
  aspis-prover/src/state_only_entropy.rs `Profile21SourceExpander::m31`:
  words are read in order from 32-byte expander blocks (8 little-endian u32
  words per block, `H(domain ‖ seed ‖ counter_le64)`); one M31 limb takes
  `candidate = word & 0x7fff_ffff` and accepts iff `candidate < P`
  (`P = 2^31 − 1`), at most 16 words (`MASK_SAMPLE_RETRY_LIMIT = 16`), else
  `MaskSampleExhausted`.
* `tryLimb` / `limbPos` / `Exhausted` mirror that loop on a word stream.
  `exhausted_window`: exhaustion ⇒ 16 consecutive rejected words starting at
  a position `≤ 16(L − 1)`; `mass_exhausted`: on uniform words the mass is
  `≤ 16 L · (2/2^32)^16`; `mass_exh_attempts`: over N attempts with two
  streams, `≤ N · 16 (L₁ + L₂) / 2^496`.
* Tree shape (binary-multiproof format, PREREG-PROOF-SIZE-2-20261019;
  r1p-readbudget/READ-BUDGET-BINARY.md): crates/aspis-r1-cost-probe/src/
  multiproof.rs `BinaryTree::new` (complete binary tree over 2^18 leaves,
  `2^(17−d)` parents at depth `d`, node input `0x12 ‖ left ‖ right`),
  host_commitment.rs (C1, C2) and prover.rs `prove_candidate_from_semantics`
  (folded tree); state_only_private_merkle.rs (leaf `0x10 ‖ tag ‖ value ‖
  salt`), state_only_entropy.rs `derive_pool_v1_leaf_salt` (one read per
  salt); each tree over `FIBRE_COUNT = 2^18` leaves with its own salts (the
  folded tree has 2^18 leaves, the values beyond 2^16 being zero).
  `CRead` is the per-attempt private commitment-read index set; its
  cardinality (`card_CRead`) is `Mc = 2 359 296 + E₁ + E₂` with `E_s` the
  expander-block budget of stream `s`; `blocks_le` bounds the blocks a
  successful stream touches by `2 L_s`; `mc_le` gives `115 + Mc ≤ 2^22`
  under the source counts (named premise `RCommitCount`), and `mc_gt_2_21`
  shows the earlier budget `2^21` fails at the worst-case counts.
* The shipped eight-way tree (aspis-core/src/r0/merkle.rs, 8^6 = 2^18
  fibres, node input `0x18 ‖ 8 children`) is kept for comparison as
  `CRead8` / `McR1_8` / `mc_le8` (`Mc = 1 685 214 + E₁ + E₂`, `≤ 2^21`). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.CommitReadsR1
open R0Z R0Z.FsAbortBounds

/-! ### A product mass lemma -/

theorem ind_forall_eq_prod {ι W : Type} [Fintype ι] [DecidableEq ι] (T : Finset ι) (Q : W → Bool)
    (ws : ι → W) [Decidable (∀ i ∈ T, Q (ws i) = true)] :
    (if ∀ i ∈ T, Q (ws i) = true then (1 : ℚ) else 0) =
      ∏ i, (if i ∈ T then (if Q (ws i) = true then (1 : ℚ) else 0) else 1) := by
  by_cases h : ∀ i ∈ T, Q (ws i) = true
  · rw [if_pos h]
    refine (Finset.prod_eq_one (fun i _ => ?_)).symm
    by_cases hi : i ∈ T
    · rw [if_pos hi, if_pos (h i hi)]
    · rw [if_neg hi]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi, hq⟩ := h
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    rw [if_pos hi, if_neg hq]

/-- On uniform `ws : ι → W`, the event "every coordinate in `T` satisfies `Q`"
has mass `(|Q|/|W|)^|T|`. -/
theorem mass_forall_mem {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [Nonempty W]
    (T : Finset ι) (Q : W → Bool) :
    mass (fun ws : ι → W => ∀ i ∈ T, Q (ws i) = true) =
      (((Finset.univ.filter (fun x => Q x = true)).card : ℚ) / Fintype.card W) ^ T.card := by
  set c : ℚ := ((Finset.univ.filter (fun x => Q x = true)).card : ℚ) with hc
  have hW : (Fintype.card W : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold mass mean
  simp only [ind_forall_eq_prod T Q]
  rw [← Fintype.prod_sum (fun i x => if i ∈ T then (if Q x = true then (1 : ℚ) else 0) else 1)]
  have hs : ∀ i, ∑ x : W, (if i ∈ T then (if Q x = true then (1 : ℚ) else 0) else 1) =
      (Fintype.card W : ℚ) * (if i ∈ T then c / Fintype.card W else 1) := by
    intro i
    by_cases hi : i ∈ T
    · simp only [if_pos hi]
      rw [Finset.sum_boole, ← hc]
      field_simp
    · simp only [if_neg hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  simp only [hs]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  push_cast
  have hp : (Fintype.card W : ℚ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hW
  field_simp

/-- An event of one coordinate of a function space has its own mass. -/
theorem mass_coord {N : ℕ} {X : Type} [Fintype X] [Nonempty X] (k : Fin N) (E : X → Prop) :
    mass (fun f : Fin N → X => E (f k)) = mass E := by
  rw [mass_equiv (R1Z.LazyTable.splitAt k)]
  have h : (fun p : X × ({j // j ≠ k} → X) => E ((R1Z.LazyTable.splitAt k).symm p k)) =
      (fun p => E p.1) := by
    funext p
    simp [R1Z.LazyTable.splitAt]
  rw [h]
  exact R0Z.FsAbortTape.mass_fst E

theorem mass_snd {R X : Type} [Fintype R] [Fintype X] [Nonempty R] (E : X → Prop) :
    mass (fun p : R × X => E p.2) = mass E := by
  rw [mass_equiv (Equiv.prodComm R X)]
  exact R0Z.FsAbortTape.mass_fst E

/-! ### The Rust word sampler -/

abbrev Word := Fin (2 ^ 32)

/-- `P = 2^31 − 1` (aspis-core field::P). -/
def P31 : ℕ := 2 ^ 31 - 1

/-- Rust: a word is rejected iff `word & 0x7fff_ffff < P` fails. -/
def rejB (x : Word) : Bool := !decide (x.val &&& 0x7fffffff < P31)

theorem rejB_iff (x : Word) : rejB x = true ↔ x.val % 2 ^ 31 = 2 ^ 31 - 1 := by
  have hm : x.val &&& 0x7fffffff = x.val % 2 ^ 31 := by
    rw [show (0x7fffffff : ℕ) = 2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : x.val % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  simp only [rejB, hm, P31, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  omega

/-- Exactly two words are rejected: `2^31 − 1` and `2^32 − 1`. -/
theorem card_rej : (Finset.univ.filter (fun x : Word => rejB x = true)).card = 2 := by
  have h : Finset.univ.filter (fun x : Word => rejB x = true) =
      {⟨2 ^ 31 - 1, by norm_num⟩, ⟨2 ^ 32 - 1, by norm_num⟩} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rejB_iff, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    have := x.isLt
    omega
  rw [h]
  rfl

variable {n : ℕ}

/-- The word at stream position `p` (positions past the stream read 0, an
accepted word; they are never reached under `16 L ≤ n`). -/
def getW (ws : Fin n → Word) (p : ℕ) : Word := if h : p < n then ws ⟨p, h⟩ else 0

/-- One limb: at most `r` words from position `p`; the position after the
accepted word, or `none` (exhausted). -/
def tryLimb (ws : Fin n → Word) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | p, r + 1 => if rejB (getW ws p) = true then tryLimb ws (p + 1) r else some (p + 1)

/-- The stream position after `l` limbs of 16 tries each. -/
def limbPos (ws : Fin n → Word) : ℕ → Option ℕ
  | 0 => some 0
  | l + 1 => (limbPos ws l).bind (fun p => tryLimb ws p 16)

/-- Limb `l`'s value (`word & 0x7fff_ffff` of its accepted word). -/
def limbVal (ws : Fin n → Word) (l : ℕ) : Option ℕ :=
  (limbPos ws (l + 1)).map (fun p => (getW ws (p - 1)).val &&& 0x7fffffff)

/-- `MaskSampleExhausted` within the first `L` limbs. -/
def Exhausted (ws : Fin n → Word) (L : ℕ) : Prop := limbPos ws L = none

theorem tryLimb_none (ws : Fin n → Word) :
    ∀ r p, tryLimb ws p r = none → ∀ k, k < r → rejB (getW ws (p + k)) = true
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | r + 1, p, h, k, hk => by
      unfold tryLimb at h
      by_cases hr : rejB (getW ws p) = true
      · rw [if_pos hr] at h
        rcases k with _ | k
        · simpa using hr
        · have := tryLimb_none ws r (p + 1) h k (by omega)
          rwa [show p + 1 + k = p + (k + 1) by omega] at this
      · rw [if_neg hr] at h
        exact absurd h (by simp)

theorem tryLimb_le (ws : Fin n → Word) :
    ∀ r p p', tryLimb ws p r = some p' → p' ≤ p + r
  | 0, _, _, h => by simp [tryLimb] at h
  | r + 1, p, p', h => by
      unfold tryLimb at h
      by_cases hr : rejB (getW ws p) = true
      · rw [if_pos hr] at h
        have := tryLimb_le ws r (p + 1) p' h
        omega
      · rw [if_neg hr] at h
        have := Option.some.inj h
        omega

theorem limbPos_le (ws : Fin n → Word) : ∀ l p, limbPos ws l = some p → p ≤ 16 * l
  | 0, p, h => by simp [limbPos] at h; omega
  | l + 1, p, h => by
      unfold limbPos at h
      rcases hl : limbPos ws l with _ | q
      · rw [hl] at h
        simp at h
      · rw [hl] at h
        have h1 := limbPos_le ws l q hl
        have h2 := tryLimb_le ws 16 q p h
        omega

/-- Exhaustion leaves 16 consecutive rejected words inside the first `16 L`. -/
theorem exhausted_window (ws : Fin n → Word) :
    ∀ L, Exhausted ws L → ∃ s, s + 16 ≤ 16 * L ∧ ∀ k, k < 16 → rejB (getW ws (s + k)) = true
  | 0, h => by simp [Exhausted, limbPos] at h
  | L + 1, h => by
      unfold Exhausted limbPos at h
      rcases hl : limbPos ws L with _ | q
      · obtain ⟨s, hs, hw⟩ := exhausted_window ws L hl
        exact ⟨s, by omega, hw⟩
      · rw [hl] at h
        have hq := limbPos_le ws L q hl
        exact ⟨q, by omega, tryLimb_none ws 16 q h⟩

/-- The words touched by a successful stream of `L` limbs fill at most `2 L`
blocks of 8 words. -/
theorem blocks_le (ws : Fin n → Word) (L p : ℕ) (h : limbPos ws L = some p) :
    (p + 7) / 8 ≤ 2 * L := by
  have := limbPos_le ws L p h
  omega

/-- The rejection rate `2 / 2^32` of one word. -/
theorem mass_rej_window (s : ℕ) (hs : s + 16 ≤ n) :
    mass (fun ws : Fin n → Word => ∀ k, k < 16 → rejB (getW ws (s + k)) = true) ≤
      ((2 : ℚ) / 2 ^ 32) ^ 16 := by
  let e : Fin 16 ↪ Fin n := ⟨fun k => ⟨s + k.val, by omega⟩, fun a b h => by
    simp only [Fin.mk.injEq, Nat.add_left_cancel_iff] at h
    exact Fin.ext h⟩
  have hm := mass_forall_mem (Finset.univ.map e) rejB
  rw [card_rej, Finset.card_map, Finset.card_univ, Fintype.card_fin, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] at hm
  rw [← hm]
  refine mass_mono _ _ (fun ws hw i hi => ?_)
  obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
  have := hw k.val k.isLt
  unfold getW at this
  rw [dif_pos (by omega)] at this
  exact this

/-- The exhaustion mass of one stream of `L` limbs on `n ≥ 16 L` uniform words. -/
theorem mass_exhausted (L : ℕ) (hn : 16 * L ≤ n) :
    mass (fun ws : Fin n → Word => Exhausted ws L) ≤ (16 * L : ℚ) * ((2 : ℚ) / 2 ^ 32) ^ 16 := by
  have hsub : ∀ ws : Fin n → Word, Exhausted ws L →
      ∃ s : Fin (16 * L), s.val + 16 ≤ 16 * L ∧
        ∀ k, k < 16 → rejB (getW ws (s.val + k)) = true := by
    intro ws h
    obtain ⟨s, hs, hw⟩ := exhausted_window ws L h
    exact ⟨⟨s, by omega⟩, hs, hw⟩
  refine (mass_mono _ _ hsub).trans ?_
  have hb := mass_exists_le_card
    (fun (s : Fin (16 * L)) (ws : Fin n → Word) => s.val + 16 ≤ 16 * L ∧
      ∀ k, k < 16 → rejB (getW ws (s.val + k)) = true)
    (((2 : ℚ) / 2 ^ 32) ^ 16) (fun s => by
      by_cases hs : s.val + 16 ≤ 16 * L
      · refine (mass_mono _ _ (fun ws h => h.2)).trans (mass_rej_window s.val (by omega))
      · rw [mass_congr _ (fun _ => False) (fun ws => ⟨fun h => hs h.1, False.elim⟩), mass_false]
        positivity)
  rw [Fintype.card_fin] at hb
  push_cast at hb
  exact hb

theorem rej_rate : ((2 : ℚ) / 2 ^ 32) ^ 16 = 1 / 2 ^ 496 := by
  rw [show (2 : ℚ) / 2 ^ 32 = 1 / 2 ^ 31 by norm_num, one_div_pow, ← pow_mul]

/-- `G-exh` for the R1 attempt loop: `N` attempts, each with the two
expander streams (SeedExpander of `L₁` limbs, Profile21 D expander of `L₂`
limbs) on independent uniform words. -/
theorem mass_exh_attempts (N L₁ L₂ n₁ n₂ : ℕ) (h₁ : 16 * L₁ ≤ n₁) (h₂ : 16 * L₂ ≤ n₂) :
    mass (fun ws : Fin N → (Fin n₁ → Word) × (Fin n₂ → Word) =>
        ∃ k, Exhausted (ws k).1 L₁ ∨ Exhausted (ws k).2 L₂) ≤
      (N : ℚ) * (16 * (L₁ + L₂)) / 2 ^ 496 := by
  have hk : ∀ k : Fin N, mass (fun ws : Fin N → (Fin n₁ → Word) × (Fin n₂ → Word) =>
      Exhausted (ws k).1 L₁ ∨ Exhausted (ws k).2 L₂) ≤ (16 * (L₁ + L₂) : ℚ) / 2 ^ 496 := by
    intro k
    rw [mass_coord k (fun p : (Fin n₁ → Word) × (Fin n₂ → Word) =>
      Exhausted p.1 L₁ ∨ Exhausted p.2 L₂)]
    refine (mass_or_le _ _).trans ?_
    rw [R0Z.FsAbortTape.mass_fst (fun ws => Exhausted ws L₁), mass_snd (fun ws => Exhausted ws L₂)]
    have e1 := mass_exhausted L₁ h₁
    have e2 := mass_exhausted L₂ h₂
    rw [rej_rate] at e1 e2
    calc _ ≤ (16 * L₁ : ℚ) * (1 / 2 ^ 496) + (16 * L₂ : ℚ) * (1 / 2 ^ 496) := add_le_add e1 e2
      _ = (16 * (L₁ + L₂) : ℚ) / 2 ^ 496 := by ring
  have hu := mass_exists_le_card _ _ hk
  rw [Fintype.card_fin] at hu
  calc _ ≤ (N : ℚ) * ((16 * (L₁ + L₂) : ℚ) / 2 ^ 496) := hu
    _ = (N : ℚ) * (16 * (L₁ + L₂)) / 2 ^ 496 := by ring

/-! ### The commitment-read count -/

/-- The source limb counts (REF R-commit, counted from state_only_hiding.rs
`build_mask_material_for_layout` and state_only_entropy.rs
`derive_pool_v1_zero_factor_d`): stream 1 draws one M31 per relation-free
C1 mask cell (at most 26·1024), 10·1024 mask-only C1 limbs, 1024 QM31 of
`g` and at most 1024 QM31 of `h1_padding`; stream 2 draws 1024 QM31 of `D`. -/
def RCommitCount (L₁ L₂ : ℕ) : Prop := L₁ ≤ 26 * 1024 + 10 * 1024 + 4 * 1024 + 4 * 1024 ∧ L₂ = 4 * 1024

/-- Per-attempt private commitment reads (binary format): salts and leaves
of the three trees (C1, C2, folded; 2^18 each), binary parents at depths
0..17 (`2^(17−d)` parents at depth `d`, the root last), the three secret
seed reads (mask seed, source-mask seed, D seed), and the expander blocks of
the two streams (budgets `E₁`, `E₂`). -/
abbrev CRead (E₁ E₂ : ℕ) :=
  (Fin 3 × Fin (2 ^ 18)) ⊕ (Fin 3 × Fin (2 ^ 18)) ⊕ (Fin 3 × (Σ d : Fin 18, Fin (2 ^ (17 - d.val)))) ⊕
    Fin 3 ⊕ (Fin E₁ ⊕ Fin E₂)

/-- A complete binary tree over 2^18 leaves has `2^18 − 1` parents. -/
theorem card_nodes : Fintype.card (Σ d : Fin 18, Fin (2 ^ (17 - d.val))) = 262143 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  first
    | (rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ (17 - i)) 18]; norm_num [Finset.sum_range_succ])
    | norm_num [Fin.sum_univ_succ]

def McR1 (E₁ E₂ : ℕ) : ℕ := 2359296 + E₁ + E₂

theorem card_CRead (E₁ E₂ : ℕ) : Fintype.card (CRead E₁ E₂) = McR1 E₁ E₂ := by
  simp only [CRead, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_nodes, McR1]
  norm_num <;> omega

/-- With the worst-case block budgets `E_s = 2 L_s` (`blocks_le`) and the
source limb counts, `115 + Mc ≤ 2^22` (the D41 read budget, binary format). -/
theorem mc_le (L₁ L₂ : ℕ) (hc : RCommitCount L₁ L₂) : 115 + McR1 (2 * L₁) (2 * L₂) ≤ 2 ^ 22 := by
  obtain ⟨h1, h2⟩ := hc
  unfold McR1
  norm_num <;> omega

/-- The earlier budget `2^21` is false for the binary format: at the
worst-case limb counts `115 + Mc = 2 457 715 > 2^21`. -/
theorem mc_gt_2_21 : 2 ^ 21 < 115 + McR1 (2 * (26 * 1024 + 10 * 1024 + 4 * 1024 + 4 * 1024)) (2 * (4 * 1024)) ∧
    RCommitCount (26 * 1024 + 10 * 1024 + 4 * 1024 + 4 * 1024) (4 * 1024) := by
  refine ⟨?_, by unfold RCommitCount; exact ⟨le_rfl, rfl⟩⟩
  unfold McR1
  norm_num

/-! ### The shipped eight-way count (comparison) -/

/-- Eight-way: 8-ary nodes at levels 1..6 (8^(5−d) nodes at level d+1, the root last). -/
abbrev CRead8 (E₁ E₂ : ℕ) :=
  (Fin 3 × Fin (2 ^ 18)) ⊕ (Fin 3 × Fin (2 ^ 18)) ⊕ (Fin 3 × (Σ d : Fin 6, Fin (8 ^ (5 - d.val)))) ⊕
    Fin 3 ⊕ (Fin E₁ ⊕ Fin E₂)

theorem card_nodes8 : Fintype.card (Σ d : Fin 6, Fin (8 ^ (5 - d.val))) = 37449 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_six]
  norm_num

def McR1_8 (E₁ E₂ : ℕ) : ℕ := 1685214 + E₁ + E₂

theorem card_CRead8 (E₁ E₂ : ℕ) : Fintype.card (CRead8 E₁ E₂) = McR1_8 E₁ E₂ := by
  simp only [CRead8, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_nodes8, McR1_8]
  norm_num <;> omega

theorem mc_le8 (L₁ L₂ : ℕ) (hc : RCommitCount L₁ L₂) : 115 + McR1_8 (2 * L₁) (2 * L₂) ≤ 2 ^ 21 := by
  obtain ⟨h1, h2⟩ := hc
  unfold McR1_8
  norm_num <;> omega

/-- The binary format adds `3 · (2^18 − 1) − 3 · 37449 = 674 082` node reads. -/
theorem McR1_sub (E₁ E₂ : ℕ) : McR1 E₁ E₂ = McR1_8 E₁ E₂ + 674082 := by
  unfold McR1 McR1_8
  omega

/-- The R1 exhaustion bound with the source counts: `εexh ≤ N / 2^476`. -/
theorem mass_exh_R1 (N L₁ L₂ : ℕ) (hc : RCommitCount L₁ L₂) :
    mass (fun ws : Fin N → (Fin (16 * L₁) → Word) × (Fin (16 * L₂) → Word) =>
        ∃ k, Exhausted (ws k).1 L₁ ∨ Exhausted (ws k).2 L₂) ≤ (N : ℚ) / 2 ^ 476 := by
  refine (mass_exh_attempts N L₁ L₂ _ _ le_rfl le_rfl).trans ?_
  obtain ⟨h1, h2⟩ := hc
  have hL : (16 * (L₁ + L₂) : ℚ) ≤ 2 ^ 20 := by
    have : 16 * (L₁ + L₂) ≤ 2 ^ 20 := by omega
    exact_mod_cast this
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  calc (N : ℚ) * (16 * (L₁ + L₂)) / 2 ^ 496 ≤ (N : ℚ) * 2 ^ 20 / 2 ^ 496 := by
        gcongr
    _ = (N : ℚ) / 2 ^ 476 := by
        rw [show (496 : ℕ) = 20 + 476 from rfl, pow_add]
        field_simp

#print axioms ind_forall_eq_prod
#print axioms mass_forall_mem
#print axioms mass_coord
#print axioms mass_snd
#print axioms rejB_iff
#print axioms card_rej
#print axioms tryLimb_none
#print axioms tryLimb_le
#print axioms limbPos_le
#print axioms exhausted_window
#print axioms blocks_le
#print axioms mass_rej_window
#print axioms mass_exhausted
#print axioms rej_rate
#print axioms mass_exh_attempts
#print axioms card_nodes
#print axioms card_CRead
#print axioms mc_le
#print axioms mc_gt_2_21
#print axioms card_nodes8
#print axioms card_CRead8
#print axioms mc_le8
#print axioms McR1_sub
#print axioms mass_exh_R1
end R1Z.CommitReadsR1
