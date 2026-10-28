import R0Z.FsAbortBounds

/-! G-prog, generic part (DESIGN-ZF1-COUPLINGS-R1 §3.1): the lazy-programming
law for a uniform random table over a finite address set.

Setting: a finite address type `A`, a finite answer type `U`, a table
`t : A → U` and `m` reads whose addresses `a i u` are CAUSAL — read `i`'s
address depends only on the answers `u j` with `j < i`.

* `prog a t u` reprograms `t` at the read addresses with the answers `u`,
  first write wins (an address read twice keeps its first answer).
* `sum_prog` / `mean_prog` (meanR): if `t` and `u` are uniform and
  independent, `prog a t u` is a uniform table.  Proof: peel the last read;
  for fixed earlier answers, `(t, v) ↦ update t x v` is `|U|`-to-one onto
  the tables (`sum_update`).
* `prog_first` / `prog_off`: the programmed table answers every
  first-occurrence read address with its coordinate and is `t` elsewhere.
* `run_unique` / `run_eq`: an adaptive run against `prog a t u` (the real
  oracle) whose addresses are pairwise distinct has exactly the answers `u`
  (the middle game's coins).  This is the agreement half of G-prog.

Everything is symbolic: no table, address set or answer type is
enumerated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.LazyTable
open R0Z R0Z.FsAbortBounds
variable {A U : Type}

/-! ### Splitting a table at one address -/

def splitAt [DecidableEq A] (x : A) : (A → U) ≃ U × ({j // j ≠ x} → U) where
  toFun t := (t x, fun j => t j.1)
  invFun p j := if h : j = x then p.1 else p.2 ⟨j, h⟩
  left_inv t := by
    funext j
    by_cases h : j = x
    · subst h
      simp
    · simp [h]
  right_inv p := by
    obtain ⟨w, r⟩ := p
    refine Prod.ext ?_ ?_
    · simp
    · funext j
      simp [j.2]

theorem update_splitAt_symm [DecidableEq A] (x : A) (w v : U) (r : {j // j ≠ x} → U) :
    Function.update ((splitAt x).symm (w, r)) x v = (splitAt x).symm (v, r) := by
  funext j
  by_cases h : j = x
  · subst h
    simp [splitAt]
  · rw [Function.update_of_ne h]
    simp [splitAt, h]

/-- `(t, v) ↦ update t x v` is `|U|`-to-one onto the tables. -/
theorem sum_update [DecidableEq A] [Fintype A] [Fintype U] (x : A) (G : (A → U) → ℚ) :
    ∑ t : A → U, ∑ v : U, G (Function.update t x v) = (Fintype.card U : ℚ) * ∑ t, G t := by
  have e1 : ∑ t : A → U, ∑ v : U, G (Function.update t x v) =
      ∑ p : U × ({j // j ≠ x} → U), ∑ v : U, G (Function.update ((splitAt x).symm p) x v) :=
    Fintype.sum_equiv (splitAt x) _ _ (fun t => by simp)
  have e2 : ∑ t : A → U, G t = ∑ p : U × ({j // j ≠ x} → U), G ((splitAt x).symm p) :=
    Fintype.sum_equiv (splitAt x) _ _ (fun t => by simp)
  rw [e1, e2, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [update_splitAt_symm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm]

/-! ### Programming, first write wins -/

variable [DecidableEq A]

/-- Program `t` at the addresses `b` with the answers `u`; the earliest
index wins (the last read is written first, then overwritten by earlier
ones). -/
def progV : (m : ℕ) → (Fin m → A) → (Fin m → U) → (A → U) → (A → U)
  | 0, _, _, t => t
  | m + 1, b, u, t =>
      progV m (Fin.init b) (Fin.init u) (Function.update t (b (Fin.last m)) (u (Fin.last m)))

/-- Read `i`'s address depends only on the answers of the reads before it. -/
def Causal {m : ℕ} (a : Fin m → (Fin m → U) → A) : Prop :=
  ∀ i u u', (∀ j, j < i → u j = u' j) → a i u = a i u'

/-- The programmed table of the adaptive reads `a` with answers `u`. -/
def prog {m : ℕ} (a : Fin m → (Fin m → U) → A) (t : A → U) (u : Fin m → U) : A → U :=
  progV m (fun i => a i u) u t

theorem progV_off : ∀ (m : ℕ) (b : Fin m → A) (u : Fin m → U) (t : A → U) (y : A),
    (∀ i, b i ≠ y) → progV m b u t y = t y
  | 0, _, _, _, _, _ => rfl
  | m + 1, b, u, t, y, hb => by
      show progV m (Fin.init b) (Fin.init u) _ y = t y
      rw [progV_off m (Fin.init b) (Fin.init u) _ y (fun i => hb _)]
      exact Function.update_of_ne (Ne.symm (hb _)) _ _

/-- A first-occurrence address is answered by its own coordinate. -/
theorem progV_first : ∀ (m : ℕ) (b : Fin m → A) (u : Fin m → U) (t : A → U) (i : Fin m),
    (∀ j, j < i → b j ≠ b i) → progV m b u t (b i) = u i
  | 0, _, _, _, i, _ => i.elim0
  | m + 1, b, u, t, i, hb => by
      show progV m (Fin.init b) (Fin.init u) _ (b i) = u i
      by_cases hi : i = Fin.last m
      · subst hi
        rw [progV_off m (Fin.init b) (Fin.init u) _ _ (fun j => hb _ (Fin.castSucc_lt_last j))]
        exact Function.update_self _ _ _
      · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi
        exact progV_first m (Fin.init b) (Fin.init u) _ i'
          (fun j hj => hb _ (Fin.castSucc_lt_castSucc_iff.mpr hj))

theorem prog_off {m : ℕ} (a : Fin m → (Fin m → U) → A) (t : A → U) (u : Fin m → U) (y : A)
    (hy : ∀ i, a i u ≠ y) : prog a t u y = t y :=
  progV_off m _ u t y hy

theorem prog_first {m : ℕ} (a : Fin m → (Fin m → U) → A) (t : A → U) (u : Fin m → U) (i : Fin m)
    (hi : ∀ j, j < i → a j u ≠ a i u) : prog a t u (a i u) = u i :=
  progV_first m _ u t i hi

/-! ### The lazy-programming law -/

section Law
variable [Fintype A] [Fintype U] [Nonempty U]

theorem causal_tail {m : ℕ} (a : Fin (m + 1) → (Fin (m + 1) → U) → A) (ha : Causal a)
    (i : Fin (m + 1)) (u : Fin m → U) (v v' : U) (hi : i = Fin.last m ∨ ∃ i', i = Fin.castSucc i') :
    a i (Fin.snoc u v) = a i (Fin.snoc u v') := by
  refine ha i _ _ (fun j hj => ?_)
  have hj' : j ≠ Fin.last m := by
    rcases hi with rfl | ⟨i', rfl⟩
    · exact ne_of_lt hj
    · exact ne_of_lt (lt_trans hj (Fin.castSucc_lt_last i'))
  obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj'
  simp only [Fin.snoc_castSucc]

/-- The read program of the first `m` reads, with the last answer fixed to `v₀`. -/
def headProg {m : ℕ} (a : Fin (m + 1) → (Fin (m + 1) → U) → A) (v₀ : U) :
    Fin m → (Fin m → U) → A :=
  fun i u => a (Fin.castSucc i) (Fin.snoc u v₀)

theorem headProg_causal {m : ℕ} (a : Fin (m + 1) → (Fin (m + 1) → U) → A) (ha : Causal a) (v₀ : U) :
    Causal (headProg a v₀) := by
  intro i u u' h
  refine ha _ _ _ (fun j hj => ?_)
  have hj' : j ≠ Fin.last m := ne_of_lt (lt_trans hj (Fin.castSucc_lt_last i))
  obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj'
  simp only [Fin.snoc_castSucc]
  exact h j' (Fin.castSucc_lt_castSucc_iff.mp hj)

theorem prog_snoc {m : ℕ} (a : Fin (m + 1) → (Fin (m + 1) → U) → A) (ha : Causal a) (v₀ : U)
    (t : A → U) (u : Fin m → U) (v : U) :
    prog a t (Fin.snoc u v) =
      prog (headProg a v₀) (Function.update t (a (Fin.last m) (Fin.snoc u v₀)) v) u := by
  show progV m (Fin.init (fun i => a i (Fin.snoc u v))) (Fin.init (Fin.snoc (α := fun _ => U) u v))
      (Function.update t (a (Fin.last m) (Fin.snoc u v)) (Fin.snoc (α := fun _ => U) u v (Fin.last m))) =
    progV m (fun i => headProg a v₀ i u) u (Function.update t (a (Fin.last m) (Fin.snoc u v₀)) v)
  rw [Fin.init_snoc, Fin.snoc_last, causal_tail a ha (Fin.last m) u v v₀ (Or.inl rfl)]
  congr 1
  funext i
  exact causal_tail a ha (Fin.castSucc i) u v v₀ (Or.inr ⟨i, rfl⟩)

/-- Sum form of the lazy-programming law. -/
theorem sum_prog : ∀ (m : ℕ) (a : Fin m → (Fin m → U) → A), Causal a → ∀ (F : (A → U) → ℚ),
    ∑ t : A → U, ∑ u : Fin m → U, F (prog a t u) =
      (Fintype.card U : ℚ) ^ m * ∑ t, F t
  | 0, a, _, F => by
      have hu : ∀ t : A → U, ∑ u : Fin 0 → U, F (prog a t u) = F t := by
        intro t
        rw [Fintype.sum_unique]
        rfl
      simp only [hu, pow_zero, one_mul]
  | m + 1, a, ha, F => by
      let v₀ : U := Classical.arbitrary U
      have hsplit : ∀ t : A → U, ∑ u : Fin (m + 1) → U, F (prog a t u) =
          ∑ u : Fin m → U, ∑ v : U,
            F (prog (headProg a v₀) (Function.update t (a (Fin.last m) (Fin.snoc u v₀)) v) u) := by
        intro t
        rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => U)) (fun p => F (prog a t (Fin.snoc p.2 p.1)))
          (fun u => F (prog a t u)) (fun p => rfl), Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
        show F (prog a t (Fin.snoc u v)) = _
        rw [prog_snoc a ha v₀]
      simp only [hsplit]
      rw [Finset.sum_comm]
      have hin : ∀ u : Fin m → U, ∑ t : A → U, ∑ v : U,
          F (prog (headProg a v₀) (Function.update t (a (Fin.last m) (Fin.snoc u v₀)) v) u) =
            (Fintype.card U : ℚ) * ∑ t, F (prog (headProg a v₀) t u) :=
        fun u => sum_update (a (Fin.last m) (Fin.snoc u v₀)) (fun t => F (prog (headProg a v₀) t u))
      simp only [hin]
      rw [← Finset.mul_sum, Finset.sum_comm, sum_prog m (headProg a v₀) (headProg_causal a ha v₀) F]
      ring

/-- The lazy-programming law (meanR of the real coupling): a uniform table
reprogrammed at causal adaptive addresses with independent uniform answers
is a uniform table. -/
theorem mean_prog {m : ℕ} (a : Fin m → (Fin m → U) → A) (ha : Causal a) (F : (A → U) → ℚ) :
    mean (fun p : (A → U) × (Fin m → U) => F (prog a p.1 p.2)) = mean F := by
  unfold mean
  have hc : Fintype.card (Fin m → U) = Fintype.card U ^ m := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [Fintype.sum_prod_type, sum_prog m a ha F, Fintype.card_prod, hc]
  have hU : (Fintype.card U : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hA : (Fintype.card (A → U) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  push_cast
  rw [mul_comm ((Fintype.card (A → U) : ℕ) : ℚ)]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hU)

end Law

/-! ### Adaptive runs against the programmed table -/

/-- Two adaptive runs against the same oracle agree (causal addresses). -/
theorem run_unique {m : ℕ} (a : Fin m → (Fin m → U) → A) (ha : Causal a) (H : A → U)
    (v w : Fin m → U) (hv : ∀ i, v i = H (a i v)) (hw : ∀ i, w i = H (a i w)) : v = w := by
  have key : ∀ n : ℕ, ∀ i : Fin m, i.val < n → v i = w i := by
    intro n
    induction n with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ n ih =>
        intro i hi
        rw [hv i, hw i, ha i v w (fun j hj => ih j (lt_of_lt_of_le (Fin.lt_def.mp hj) (Nat.lt_succ_iff.mp hi)))]
  funext i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

/-- The real run against `prog a t u` reads exactly the middle answers `u`
when the read addresses are pairwise distinct (no collision). -/
theorem run_eq {m : ℕ} (a : Fin m → (Fin m → U) → A) (ha : Causal a) (t : A → U) (u : Fin m → U)
    (hd : ∀ i j, j < i → a j u ≠ a i u) (v : Fin m → U)
    (hv : ∀ i, v i = prog a t u (a i v)) : v = u :=
  run_unique a ha (prog a t u) v u hv (fun i => (prog_first a t u i (hd i)).symm)

#print axioms splitAt
#print axioms update_splitAt_symm
#print axioms sum_update
#print axioms progV_off
#print axioms progV_first
#print axioms prog_off
#print axioms prog_first
#print axioms causal_tail
#print axioms headProg_causal
#print axioms prog_snoc
#print axioms sum_prog
#print axioms mean_prog
#print axioms run_unique
#print axioms run_eq
end R1Z.LazyTable
