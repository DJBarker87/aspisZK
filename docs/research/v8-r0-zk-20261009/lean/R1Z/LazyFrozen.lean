import R1Z.LazyTable

/-! G-prog with a frozen part of the table (DESIGN-R1-REAL §2).

The R1 prover reads one address of the table that is never programmed: the
statement digest `H(public_bytes)` (a public address, read by every attempt
and by the adversary).  Its value enters the prover's private addresses.  So
the read addresses may depend on the table, but only on a fixed finite
FROZEN set `Fr` of addresses, and programming skips writes into `Fr`.

* `progF`: first-write-wins programming that never writes into `Fr`;
* `mean_progF`: with uniform independent `t` and `u` the programmed table is
  uniform (exact; the frozen values are never moved);
* `progF_frozen`, `progF_first`, `progF_off`;
* `runC` / `runC_spec`: the honest in-order evaluation of a causal read
  program against an oracle, with unread answers defaulted (partial
  vectors), is a fixpoint;
* `run_eqF`: off collisions and off `Fr`, the honest run against the
  programmed table has exactly the lazy answers `u`. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.LazyFrozen
open R0Z R0Z.FsAbortBounds R1Z.LazyTable

variable {A U : Type} [DecidableEq A]

/-! ### Programming that skips the frozen set -/

def progFV (Fr : Finset A) : (m : ℕ) → (Fin m → A) → (Fin m → U) → (A → U) → (A → U)
  | 0, _, _, t => t
  | m + 1, b, u, t =>
      progFV Fr m (Fin.init b) (Fin.init u)
        (if b (Fin.last m) ∈ Fr then t else Function.update t (b (Fin.last m)) (u (Fin.last m)))

/-- Read `i`'s address depends on the answers before `i` and on the table
only through the frozen set. -/
def CausalF (Fr : Finset A) {m : ℕ} (a : Fin m → (Fin m → U) → (A → U) → A) : Prop :=
  ∀ i u u' t t', (∀ j, j < i → u j = u' j) → (∀ y ∈ Fr, t y = t' y) → a i u t = a i u' t'

def progF (Fr : Finset A) {m : ℕ} (a : Fin m → (Fin m → U) → (A → U) → A) (t : A → U)
    (u : Fin m → U) : A → U :=
  progFV Fr m (fun i => a i u t) u t

theorem progFV_frozen (Fr : Finset A) : ∀ (m : ℕ) (b : Fin m → A) (u : Fin m → U) (t : A → U)
    (y : A), y ∈ Fr → progFV Fr m b u t y = t y
  | 0, _, _, _, _, _ => rfl
  | m + 1, b, u, t, y, hy => by
      show progFV Fr m (Fin.init b) (Fin.init u) _ y = t y
      rw [progFV_frozen Fr m _ _ _ y hy]
      by_cases hb : b (Fin.last m) ∈ Fr
      · rw [if_pos hb]
      · rw [if_neg hb]
        exact Function.update_of_ne (fun e => hb (by rw [← e]; exact hy)) _ _

theorem progFV_off (Fr : Finset A) : ∀ (m : ℕ) (b : Fin m → A) (u : Fin m → U) (t : A → U)
    (y : A), (∀ i, b i ≠ y) → progFV Fr m b u t y = t y
  | 0, _, _, _, _, _ => rfl
  | m + 1, b, u, t, y, hb => by
      show progFV Fr m (Fin.init b) (Fin.init u) _ y = t y
      rw [progFV_off Fr m (Fin.init b) (Fin.init u) _ y (fun i => hb _)]
      by_cases hl : b (Fin.last m) ∈ Fr
      · rw [if_pos hl]
      · rw [if_neg hl]
        exact Function.update_of_ne (Ne.symm (hb _)) _ _

theorem progFV_first (Fr : Finset A) : ∀ (m : ℕ) (b : Fin m → A) (u : Fin m → U) (t : A → U)
    (i : Fin m), b i ∉ Fr → (∀ j, j < i → b j ≠ b i) → progFV Fr m b u t (b i) = u i
  | 0, _, _, _, i, _, _ => i.elim0
  | m + 1, b, u, t, i, hf, hb => by
      show progFV Fr m (Fin.init b) (Fin.init u) _ (b i) = u i
      by_cases hi : i = Fin.last m
      · subst hi
        rw [progFV_off Fr m (Fin.init b) (Fin.init u) _ _ (fun j => hb _ (Fin.castSucc_lt_last j)),
          if_neg hf]
        exact Function.update_self _ _ _
      · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi
        exact progFV_first Fr m (Fin.init b) (Fin.init u) _ i' hf
          (fun j hj => hb _ (Fin.castSucc_lt_castSucc_iff.mpr hj))

theorem progF_frozen (Fr : Finset A) {m : ℕ} (a : Fin m → (Fin m → U) → (A → U) → A)
    (t : A → U) (u : Fin m → U) (y : A) (hy : y ∈ Fr) : progF Fr a t u y = t y :=
  progFV_frozen Fr m _ u t y hy

theorem progF_off (Fr : Finset A) {m : ℕ} (a : Fin m → (Fin m → U) → (A → U) → A)
    (t : A → U) (u : Fin m → U) (y : A) (hy : ∀ i, a i u t ≠ y) : progF Fr a t u y = t y :=
  progFV_off Fr m _ u t y hy

theorem progF_first (Fr : Finset A) {m : ℕ} (a : Fin m → (Fin m → U) → (A → U) → A)
    (t : A → U) (u : Fin m → U) (i : Fin m) (hf : a i u t ∉ Fr)
    (hi : ∀ j, j < i → a j u t ≠ a i u t) : progF Fr a t u (a i u t) = u i :=
  progFV_first Fr m _ u t i hf hi

/-! ### The frozen update is `|U|`-to-one -/

/-- One frozen-aware write. -/
def upd (Fr : Finset A) (t : A → U) (x : A) (v : U) : A → U :=
  if x ∈ Fr then t else Function.update t x v

theorem upd_frozen (Fr : Finset A) (t : A → U) (x : A) (v : U) (y : A) (hy : y ∈ Fr) :
    upd Fr t x v y = t y := by
  unfold upd
  by_cases hx : x ∈ Fr
  · rw [if_pos hx]
  · rw [if_neg hx]
    exact Function.update_of_ne (fun e => hx (by rw [← e]; exact hy)) _ _

def splitFr (Fr : Finset A) : (A → U) ≃ ({a // a ∈ Fr} → U) × ({a // a ∉ Fr} → U) where
  toFun t := (fun a => t a.1, fun a => t a.1)
  invFun p a := if h : a ∈ Fr then p.1 ⟨a, h⟩ else p.2 ⟨a, h⟩
  left_inv t := by
    funext a
    by_cases h : a ∈ Fr <;> simp [h]
  right_inv p := by
    obtain ⟨f, r⟩ := p
    refine Prod.ext ?_ ?_
    · funext a
      simp [a.2]
    · funext a
      simp [a.2]

theorem splitFr_symm_frozen (Fr : Finset A) (f : {a // a ∈ Fr} → U) (r r' : {a // a ∉ Fr} → U)
    (y : A) (hy : y ∈ Fr) : (splitFr Fr).symm (f, r) y = (splitFr Fr).symm (f, r') y := by
  simp [splitFr, hy]

theorem update_splitFr_symm (Fr : Finset A) (f : {a // a ∈ Fr} → U) (r : {a // a ∉ Fr} → U)
    (x : A) (hx : x ∉ Fr) (v : U) :
    Function.update ((splitFr Fr).symm (f, r)) x v = (splitFr Fr).symm (f, Function.update r ⟨x, hx⟩ v) := by
  funext a
  by_cases ha : a ∈ Fr
  · have hne : a ≠ x := fun e => hx (e ▸ ha)
    rw [Function.update_of_ne hne]
    simp [splitFr, ha]
  · by_cases hax : a = x
    · subst hax
      simp [splitFr, ha]
    · rw [Function.update_of_ne hax]
      have hne : (⟨a, ha⟩ : {a // a ∉ Fr}) ≠ ⟨x, hx⟩ := fun e => hax (congrArg Subtype.val e)
      simp [splitFr, ha, Function.update_of_ne hne]

theorem sum_updF (Fr : Finset A) [Fintype A] [Fintype U] [Nonempty U] (x : (A → U) → A)
    (hx : ∀ t t', (∀ y ∈ Fr, t y = t' y) → x t = x t') (G : (A → U) → ℚ) :
    ∑ t : A → U, ∑ v : U, G (upd Fr t (x t) v) = (Fintype.card U : ℚ) * ∑ t, G t := by
  have e1 : ∑ t : A → U, ∑ v : U, G (upd Fr t (x t) v) =
      ∑ p : ({a // a ∈ Fr} → U) × ({a // a ∉ Fr} → U), ∑ v : U,
        G (upd Fr ((splitFr Fr).symm p) (x ((splitFr Fr).symm p)) v) :=
    Fintype.sum_equiv (splitFr Fr) _ _ (fun t => by simp)
  have e2 : ∑ t : A → U, G t = ∑ p : ({a // a ∈ Fr} → U) × ({a // a ∉ Fr} → U),
      G ((splitFr Fr).symm p) :=
    Fintype.sum_equiv (splitFr Fr) _ _ (fun t => by simp)
  rw [e1, e2, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  let r₀ : {a // a ∉ Fr} → U := fun a => (splitFr Fr).symm (f, fun _ => Classical.arbitrary U) a.1
  have hX : ∀ r, x ((splitFr Fr).symm (f, r)) = x ((splitFr Fr).symm (f, r₀)) :=
    fun r => hx _ _ (fun y hy => splitFr_symm_frozen Fr f r r₀ y hy)
  simp only [hX]
  by_cases hm : x ((splitFr Fr).symm (f, r₀)) ∈ Fr
  · simp only [upd, if_pos hm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  · simp only [upd, if_neg hm]
    simp only [update_splitFr_symm Fr f _ _ hm]
    exact sum_update (⟨_, hm⟩ : {a // a ∉ Fr}) (fun r => G ((splitFr Fr).symm (f, r)))

/-! ### The frozen lazy-programming law -/

section Law
variable [Fintype A] [Fintype U] [Nonempty U]

def headF {m : ℕ} (a : Fin (m + 1) → (Fin (m + 1) → U) → (A → U) → A) (v₀ : U) :
    Fin m → (Fin m → U) → (A → U) → A :=
  fun i u t => a (Fin.castSucc i) (Fin.snoc u v₀) t

omit [Fintype A] [Fintype U] [Nonempty U] in
theorem snoc_agree {m : ℕ} (u : Fin m → U) (v v' : U)
    (j : Fin (m + 1)) (hj : j ≠ Fin.last m) :
    Fin.snoc (α := fun _ => U) u v j = Fin.snoc (α := fun _ => U) u v' j := by
  obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
  simp only [Fin.snoc_castSucc]

theorem causalF_tail (Fr : Finset A) {m : ℕ} (a : Fin (m + 1) → (Fin (m + 1) → U) → (A → U) → A)
    (ha : CausalF Fr a) (i : Fin (m + 1)) (u : Fin m → U) (v v' : U) (t t' : A → U)
    (ht : ∀ y ∈ Fr, t y = t' y) :
    a i (Fin.snoc u v) t = a i (Fin.snoc u v') t' ∨ i = Fin.last m := by
  by_cases hi : i = Fin.last m
  · exact Or.inr hi
  · left
    refine ha i _ _ t t' (fun j hj => ?_) ht
    have hj' : j ≠ Fin.last m := by
      obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      exact ne_of_lt (lt_trans hj (Fin.castSucc_lt_last i'))
    exact snoc_agree u v v' j hj'

theorem causalF_last (Fr : Finset A) {m : ℕ} (a : Fin (m + 1) → (Fin (m + 1) → U) → (A → U) → A)
    (ha : CausalF Fr a) (u : Fin m → U) (v v' : U) (t t' : A → U) (ht : ∀ y ∈ Fr, t y = t' y) :
    a (Fin.last m) (Fin.snoc u v) t = a (Fin.last m) (Fin.snoc u v') t' :=
  ha _ _ _ t t' (fun j hj => snoc_agree u v v' j (ne_of_lt hj)) ht

theorem headF_causal (Fr : Finset A) {m : ℕ} (a : Fin (m + 1) → (Fin (m + 1) → U) → (A → U) → A)
    (ha : CausalF Fr a) (v₀ : U) : CausalF Fr (headF a v₀) := by
  intro i u u' t t' h ht
  refine ha _ _ _ t t' (fun j hj => ?_) ht
  have hj' : j ≠ Fin.last m := ne_of_lt (lt_trans hj (Fin.castSucc_lt_last i))
  obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj'
  simp only [Fin.snoc_castSucc]
  exact h j' (Fin.castSucc_lt_castSucc_iff.mp hj)

theorem progF_snoc (Fr : Finset A) {m : ℕ} (a : Fin (m + 1) → (Fin (m + 1) → U) → (A → U) → A)
    (ha : CausalF Fr a) (v₀ : U) (t : A → U) (u : Fin m → U) (v : U) :
    progF Fr a t (Fin.snoc u v) =
      progF Fr (headF a v₀) (upd Fr t (a (Fin.last m) (Fin.snoc u v₀) t) v) u := by
  show progFV Fr m (Fin.init (fun i => a i (Fin.snoc u v) t)) (Fin.init (Fin.snoc (α := fun _ => U) u v))
      (if a (Fin.last m) (Fin.snoc u v) t ∈ Fr then t else
        Function.update t (a (Fin.last m) (Fin.snoc u v) t) (Fin.snoc (α := fun _ => U) u v (Fin.last m))) =
    progFV Fr m (fun i => headF a v₀ i u (upd Fr t (a (Fin.last m) (Fin.snoc u v₀) t) v)) u
      (upd Fr t (a (Fin.last m) (Fin.snoc u v₀) t) v)
  rw [Fin.init_snoc, Fin.snoc_last, causalF_last Fr a ha u v v₀ t t (fun _ _ => rfl)]
  congr 1
  funext i
  show a (Fin.castSucc i) (Fin.snoc u v) t =
    a (Fin.castSucc i) (Fin.snoc u v₀) (upd Fr t (a (Fin.last m) (Fin.snoc u v₀) t) v)
  rcases causalF_tail Fr a ha (Fin.castSucc i) u v v₀ t _
      (fun y hy => (upd_frozen Fr t _ v y hy).symm) with h | h
  · exact h
  · exact absurd h (ne_of_lt (Fin.castSucc_lt_last i))

theorem sum_progF (Fr : Finset A) : ∀ (m : ℕ) (a : Fin m → (Fin m → U) → (A → U) → A),
    CausalF Fr a → ∀ (F : (A → U) → ℚ),
    ∑ t : A → U, ∑ u : Fin m → U, F (progF Fr a t u) = (Fintype.card U : ℚ) ^ m * ∑ t, F t
  | 0, a, _, F => by
      have hu : ∀ t : A → U, ∑ u : Fin 0 → U, F (progF Fr a t u) = F t := by
        intro t
        rw [Fintype.sum_unique]
        rfl
      simp only [hu, pow_zero, one_mul]
  | m + 1, a, ha, F => by
      let v₀ : U := Classical.arbitrary U
      have hsplit : ∀ t : A → U, ∑ u : Fin (m + 1) → U, F (progF Fr a t u) =
          ∑ u : Fin m → U, ∑ v : U,
            F (progF Fr (headF a v₀) (upd Fr t (a (Fin.last m) (Fin.snoc u v₀) t) v) u) := by
        intro t
        rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => U))
          (fun p => F (progF Fr a t (Fin.snoc p.2 p.1))) (fun u => F (progF Fr a t u)) (fun p => rfl),
          Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
        show F (progF Fr a t (Fin.snoc u v)) = _
        rw [progF_snoc Fr a ha v₀]
      simp only [hsplit]
      rw [Finset.sum_comm]
      have hin : ∀ u : Fin m → U, ∑ t : A → U, ∑ v : U,
          F (progF Fr (headF a v₀) (upd Fr t (a (Fin.last m) (Fin.snoc u v₀) t) v) u) =
            (Fintype.card U : ℚ) * ∑ t, F (progF Fr (headF a v₀) t u) :=
        fun u => sum_updF Fr (fun t => a (Fin.last m) (Fin.snoc u v₀) t)
          (fun t t' ht => causalF_last Fr a ha u v₀ v₀ t t' ht)
          (fun t => F (progF Fr (headF a v₀) t u))
      simp only [hin]
      rw [← Finset.mul_sum, Finset.sum_comm,
        sum_progF Fr m (headF a v₀) (headF_causal Fr a ha v₀) F]
      ring

/-- The frozen lazy-programming law. -/
theorem mean_progF (Fr : Finset A) {m : ℕ} (a : Fin m → (Fin m → U) → (A → U) → A)
    (ha : CausalF Fr a) (F : (A → U) → ℚ) :
    mean (fun p : (A → U) × (Fin m → U) => F (progF Fr a p.1 p.2)) = mean F := by
  unfold mean
  have hc : Fintype.card (Fin m → U) = Fintype.card U ^ m := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [Fintype.sum_prod_type, sum_progF Fr m a ha F, Fintype.card_prod, hc]
  have hU : (Fintype.card U : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  push_cast
  rw [mul_comm ((Fintype.card (A → U) : ℕ) : ℚ)]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hU)

end Law

/-! ### The honest in-order run -/

section Run
variable {B : Type}

/-- Evaluate reads `0 … n−1` in order; read `i`'s address is computed on the
answers so far (later answers read as `d₀`). -/
def runN {m : ℕ} (a : Fin m → (Fin m → U) → B) (H : B → U) (d₀ : U) : ℕ → (Fin m → U)
  | 0 => fun _ => d₀
  | n + 1 => if h : n < m then Function.update (runN a H d₀ n) ⟨n, h⟩ (H (a ⟨n, h⟩ (runN a H d₀ n)))
      else runN a H d₀ n

theorem runN_succ {m : ℕ} (a : Fin m → (Fin m → U) → B) (H : B → U) (d₀ : U) (n : ℕ) :
    runN a H d₀ (n + 1) = if h : n < m then Function.update (runN a H d₀ n) ⟨n, h⟩
      (H (a ⟨n, h⟩ (runN a H d₀ n))) else runN a H d₀ n := rfl

def runC {m : ℕ} (a : Fin m → (Fin m → U) → B) (H : B → U) (d₀ : U) : Fin m → U :=
  runN a H d₀ m

theorem runN_stable {m : ℕ} (a : Fin m → (Fin m → U) → B) (H : B → U) (d₀ : U) (n : ℕ)
    (i : Fin m) (hi : i.val < n) : ∀ k, runN a H d₀ (n + k) i = runN a H d₀ n i
  | 0 => rfl
  | k + 1 => by
      show runN a H d₀ (n + k + 1) i = _
      rw [runN_succ]
      split_ifs with h
      · rw [Function.update_of_ne (fun e => by
          have := congrArg Fin.val e
          simp at this
          omega)]
        exact runN_stable a H d₀ n i hi k
      · exact runN_stable a H d₀ n i hi k

theorem runN_le {m : ℕ} (a : Fin m → (Fin m → U) → B) (H : B → U) (d₀ : U) (n n' : ℕ)
    (hn : n ≤ n') (i : Fin m) (hi : i.val < n) : runN a H d₀ n' i = runN a H d₀ n i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact runN_stable a H d₀ n i hi k

theorem runN_at {m : ℕ} (a : Fin m → (Fin m → U) → B) (H : B → U) (d₀ : U) (i : Fin m) :
    runN a H d₀ (i.val + 1) i = H (a i (runN a H d₀ i.val)) := by
  show (if h : i.val < m then Function.update (runN a H d₀ i.val) ⟨i.val, h⟩
      (H (a ⟨i.val, h⟩ (runN a H d₀ i.val))) else runN a H d₀ i.val) i = _
  rw [dif_pos i.isLt]
  simp

/-- The honest run is a fixpoint of its causal read program. -/
theorem runC_spec {m : ℕ} (a : Fin m → (Fin m → U) → B) (H : B → U) (d₀ : U)
    (hc : ∀ i v v', (∀ j, j < i → v j = v' j) → a i v = a i v') (i : Fin m) :
    runC a H d₀ i = H (a i (runC a H d₀)) := by
  unfold runC
  rw [runN_le a H d₀ (i.val + 1) m i.isLt i (Nat.lt_succ_self _), runN_at]
  congr 1
  refine hc i _ _ (fun j hj => ?_)
  exact (runN_le a H d₀ i.val m (le_of_lt i.isLt) j (Fin.lt_def.mp hj)).symm

end Run

/-- Off `Fr` and off collisions, a run against the programmed table reads
exactly the lazy answers. -/
theorem run_eqF (Fr : Finset A) {m : ℕ} (a : Fin m → (Fin m → U) → (A → U) → A)
    (ha : CausalF Fr a) (t : A → U) (u : Fin m → U)
    (hf : ∀ i, a i u t ∉ Fr) (hd : ∀ i j, j < i → a j u t ≠ a i u t) (v : Fin m → U)
    (hv : ∀ i, v i = progF Fr a t u (a i v (progF Fr a t u))) : v = u := by
  have hfz : ∀ y ∈ Fr, progF Fr a t u y = t y := fun y hy => progF_frozen Fr a t u y hy
  have hc : R1Z.LazyTable.Causal (fun i (w : Fin m → U) => a i w t) :=
    fun i w w' h => ha i w w' t t h (fun _ _ => rfl)
  refine R1Z.LazyTable.run_unique (fun i (w : Fin m → U) => a i w t) hc (progF Fr a t u) v u
    (fun i => ?_) (fun i => (progF_first Fr a t u i (hf i) (hd i)).symm)
  rw [hv i, ha i v v _ t (fun _ _ => rfl) hfz]

#print axioms progFV_frozen
#print axioms progFV_off
#print axioms progFV_first
#print axioms progF_frozen
#print axioms progF_off
#print axioms progF_first
#print axioms upd_frozen
#print axioms splitFr
#print axioms update_splitFr_symm
#print axioms sum_updF
#print axioms headF_causal
#print axioms progF_snoc
#print axioms sum_progF
#print axioms mean_progF
#print axioms runN_le
#print axioms runN_at
#print axioms runC_spec
#print axioms run_eqF
end R1Z.LazyFrozen
