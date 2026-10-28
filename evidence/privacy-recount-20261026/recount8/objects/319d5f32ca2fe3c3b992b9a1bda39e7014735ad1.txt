import R1Z.LayoutR1P2Bin

/-! BINARY format (copy of `LayoutR1P3`: designated child 1, `openedQ` with `u / 2^(level+1)`). The commitment layout, part 3 (DESIGN-R1-REAL §3): who reads each
designated field (`rd_*`), the pair table `fresh_or_sep`, the opened reads
and `hidden`. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.LayoutR1PBin
open R0Z.FsStatement R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1PBin

section Readers
variable {E₁ E₂ : ℕ}

theorem rd_rootChild (c' : CPos E₁ E₂) (T : Fin 3) (j₀ : Fin 2) (h : depS c' (.inr (rootChild T j₀))) :
    c' = .inl T := by
  rcases c' with T' | (c1 | c1) | (b | i | ⟨T', v⟩ | ⟨T', v⟩ | ⟨T', n⟩)
  · obtain ⟨j, e⟩ := h
    rw [(rootChild_inj _ _ _ _ (Sum.inr.inj e)).1]
  · simp [depS, rootChild, qNode, qSeed] at h
  · simp [depS, rootChild, qNode, qSeed] at h
  · by_cases hb : b.val = 0 <;> simp [depS, hb, rootChild, qNode, qBind] at h
  · by_cases hi : i.val = 2 <;> simp [depS, hi, rootChild, qNode, qBind, qSeed] at h
  · simp [depS, rootChild, qNode, qBind] at h
  · simp [depS, rootChild, qNode, qSalt] at h
  · obtain ⟨j, e⟩ := h
    exact absurd (Sum.inr.inj e).symm (childQ_ne_rootChild _ _ _ _ _)

theorem rd_childQ (c' : CPos E₁ E₂) (T : Fin 3) (n : NodeIdx) (j₀ : Fin 2)
    (h : depS c' (.inr (childQ T n j₀))) : c' = .inr (.inr (qNode T n)) := by
  rcases c' with T' | (c1 | c1) | (b | i | ⟨T', v⟩ | ⟨T', v⟩ | ⟨T', n'⟩)
  · obtain ⟨j, e⟩ := h
    exact absurd (Sum.inr.inj e) (childQ_ne_rootChild _ _ _ _ _)
  · exact absurd (Sum.inr.inj (show _ = _ from h)) (childQ_ne_seed _ _ _ _)
  · exact absurd (Sum.inr.inj (show _ = _ from h)) (childQ_ne_seed _ _ _ _)
  · by_cases hb : b.val = 0
    · simp [depS, hb] at h
    · simp only [depS, hb, if_false] at h
      rcases h with h | h
      · exact absurd h (by simp)
      · exact absurd (Sum.inr.inj h) (childQ_ne_bind _ _ _ _)
  · by_cases hi : i.val = 2
    · simp only [depS, hi, if_true] at h
      rcases h with h | h
      · exact absurd (Sum.inr.inj h) (childQ_ne_bind _ _ _ _)
      · exact absurd (Sum.inr.inj h) (childQ_ne_seed _ _ _ _)
    · simp only [depS, hi, if_false] at h
      rcases h with h | h | h
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · exact absurd (Sum.inr.inj h) (childQ_ne_bind _ _ _ _)
  · simp only [depS] at h
    rcases h with h | h | h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd (Sum.inr.inj h) (childQ_ne_bind _ _ _ _)
  · exact absurd (Sum.inr.inj (show _ = _ from h)) (childQ_ne_salt _ _ _ _ _)
  · obtain ⟨j, e⟩ := h
    obtain ⟨hT, hn, _⟩ := childQ_inj _ _ _ _ _ _ (Sum.inr.inj e)
    rw [hT, hn]
    rfl

theorem rd_salt (c' : CPos E₁ E₂) (T : Fin 3) (u : Fib) (h : depS c' (.inr (qSalt T u))) :
    c' = .inr (.inr (qLeaf T u)) := by
  rcases c' with T' | (c1 | c1) | (b | i | ⟨T', v⟩ | ⟨T', v⟩ | ⟨T', n⟩)
  · obtain ⟨j, e⟩ := h
    simp [rootChild, qNode, qSalt] at e
  · simp [depS, qSalt, qSeed] at h
  · simp [depS, qSalt, qSeed] at h
  · by_cases hb : b.val = 0 <;> simp [depS, hb, qSalt, qBind] at h
  · by_cases hi : i.val = 2 <;> simp [depS, hi, qSalt, qBind, qSeed] at h
  · simp [depS, qSalt, qBind] at h
  · simp only [depS, qSalt, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · obtain ⟨j, e⟩ := h
    exact absurd (Sum.inr.inj e).symm (childQ_ne_salt _ _ _ _ _)

theorem rd_seed (c' : CPos E₁ E₂) (k : Fin 3) (h : depS c' (.inr (qSeed k))) :
    (k.val = 0 ∧ ∃ c1, c' = .inr (.inl (.inl c1))) ∨ (k.val = 2 ∧ ∃ c1, c' = .inr (.inl (.inr c1))) ∨
      (k.val = 1 ∧ ∃ i : Fin 3, i.val = 2 ∧ c' = .inr (.inr (qSeed i))) := by
  rcases c' with T' | (c1 | c1) | (b | i | ⟨T', v⟩ | ⟨T', v⟩ | ⟨T', n⟩)
  · obtain ⟨j, e⟩ := h
    simp [rootChild, qNode, qSeed] at e
  · simp only [depS, qSeed, Sum.inr.injEq, Sum.inl.injEq] at h
    exact Or.inl ⟨by simp [h], c1, rfl⟩
  · simp only [depS, qSeed, Sum.inr.injEq, Sum.inl.injEq] at h
    exact Or.inr (Or.inl ⟨by simp [h], c1, rfl⟩)
  · by_cases hb : b.val = 0 <;> simp [depS, hb, qSeed, qBind] at h
  · by_cases hi : i.val = 2
    · simp only [depS, hi, if_true] at h
      rcases h with h | h
      · simp [qSeed, qBind] at h
      · simp only [qSeed, Sum.inr.injEq, Sum.inl.injEq] at h
        exact Or.inr (Or.inr ⟨by rw [h]; rfl, i, hi, rfl⟩)
    · simp [depS, hi, qSeed, qBind] at h
  · simp [depS, qSeed, qBind] at h
  · simp [depS, qSeed, qSalt] at h
  · obtain ⟨j, e⟩ := h
    exact absurd (Sum.inr.inj e).symm (childQ_ne_seed _ _ _ _)

theorem rd_bind0 (c' : CPos E₁ E₂) (h : depS c' (.inr (qBind 0))) :
    (∃ b : Fin 2, b.val ≠ 0 ∧ c' = .inr (.inr (qBind b))) ∨
      (∃ i : Fin 3, i.val ≠ 2 ∧ c' = .inr (.inr (qSeed i))) := by
  rcases c' with T' | (c1 | c1) | (b | i | ⟨T', v⟩ | ⟨T', v⟩ | ⟨T', n⟩)
  · obtain ⟨j, e⟩ := h
    simp [rootChild, qNode, qBind] at e
  · simp [depS, qSeed, qBind] at h
  · simp [depS, qSeed, qBind] at h
  · by_cases hb : b.val = 0
    · simp [depS, hb] at h
    · exact Or.inl ⟨b, hb, rfl⟩
  · by_cases hi : i.val = 2
    · simp only [depS, hi, if_true] at h
      rcases h with h | h
      · simp only [qBind, Sum.inr.injEq, Sum.inl.injEq] at h
        exact absurd h (by decide)
      · simp [qSeed, qBind] at h
    · exact Or.inr ⟨i, hi, rfl⟩
  · simp only [depS] at h
    rcases h with h | h | h
    · simp at h
    · simp at h
    · simp only [qBind, Sum.inr.injEq, Sum.inl.injEq] at h
      exact absurd h (by decide)
  · simp [depS, qSalt, qBind] at h
  · obtain ⟨j, e⟩ := h
    exact absurd (Sum.inr.inj e).symm (childQ_ne_bind _ _ _ _)

theorem rd_sec (c' : CPos E₁ E₂) (k : Fin 3) (h : depS c' (.inl k)) :
    (k.val = 0 ∧ ∃ b : Fin 2, c' = .inr (.inr (qBind b))) ∨
      (k.val ≠ 2 ∧ ∃ i : Fin 3, i.val ≠ 2 ∧ c' = .inr (.inr (qSeed i))) ∨
      (k.val ≠ 1 ∧ ∃ T u, c' = .inr (.inr (qSalt T u))) := by
  rcases c' with T' | (c1 | c1) | (b | i | ⟨T', v⟩ | ⟨T', v⟩ | ⟨T', n⟩)
  · obtain ⟨j, e⟩ := h
    simp at e
  · simp [depS] at h
  · simp [depS] at h
  · refine Or.inl ⟨?_, b, rfl⟩
    by_cases hb : b.val = 0
    · simp only [depS, hb, if_true, Sum.inl.injEq] at h
      rw [h]; rfl
    · simp only [depS, hb, if_false] at h
      rcases h with h | h
      · rw [Sum.inl.inj h]; rfl
      · simp at h
  · by_cases hi : i.val = 2
    · simp [depS, hi] at h
    · simp only [depS, hi, if_false] at h
      refine Or.inr (Or.inl ⟨?_, i, hi, rfl⟩)
      rcases h with h | h | h
      · rw [Sum.inl.inj h]; decide
      · rw [Sum.inl.inj h]; decide
      · simp at h
  · simp only [depS] at h
    refine Or.inr (Or.inr ⟨?_, T', v, rfl⟩)
    rcases h with h | h | h
    · rw [Sum.inl.inj h]; decide
    · rw [Sum.inl.inj h]; decide
    · simp at h
  · simp [depS] at h
  · obtain ⟨j, e⟩ := h
    simp at e

end Readers

/-! ### The pair table -/

section Pairs
variable {E₁ E₂ : ℕ}

/-- Two distinct commitment reads: one does not read the other's designated
field, or their addresses differ for every input. -/
theorem fresh_or_sep (hE₁ : E₁ ≤ 2 ^ 64) (hE₂ : E₂ ≤ 2 ^ 64) (c c' : CPos E₁ E₂) (hne : c ≠ c') :
    ¬ depS c' (src c) ∨ ¬ depS c (src c') ∨
      ∀ pub vtag lv sec d rest, gram pub vtag lv sec d rest c ≠ gram pub vtag lv sec d rest c' := by
  rcases c with T | (c0 | c0) | (b | i | ⟨T, u⟩ | ⟨T, u⟩ | ⟨T, n⟩)
  · exact Or.inl (fun h => hne (rd_rootChild c' T 1 h).symm)
  · by_cases h : depS c' (.inr (qSeed 0))
    · rcases rd_seed c' 0 h with ⟨_, c1, rfl⟩ | ⟨h2, _⟩ | ⟨h1, _⟩
      · refine Or.inr (Or.inr (fun pub vtag lv sec d rest => sep_exp1 pub vtag lv sec d rest hE₁ c0 c1
          (fun e => hne (by rw [e]))))
      · exact absurd h2 (by decide)
      · exact absurd h1 (by decide)
    · exact Or.inl h
  · by_cases h : depS c' (.inr (qSeed 2))
    · rcases rd_seed c' 2 h with ⟨h0, _⟩ | ⟨_, c1, rfl⟩ | ⟨h1, _⟩
      · exact absurd h0 (by decide)
      · refine Or.inr (Or.inr (fun pub vtag lv sec d rest => sep_exp2 pub vtag lv sec d rest hE₂ c0 c1
          (fun e => hne (by rw [e]))))
      · exact absurd h1 (by decide)
    · exact Or.inl h
  · by_cases hb : b.val = 0
    · -- src = nonce; the precommit binding reads only the nonce
      refine Or.inr (Or.inl (fun h => ?_))
      simp only [depS, hb, if_true] at h
      rcases c' with T' | (c1 | c1) | (b' | i' | ⟨T', v⟩ | ⟨T', v⟩ | ⟨T', n'⟩)
      · simp [src] at h
      · simp [src] at h
      · simp [src] at h
      · by_cases hb' : b'.val = 0
        · exact hne (by rw [show b = b' from Fin.ext (by rw [hb, hb'])])
        · simp [src, hb'] at h
      · by_cases hi' : i'.val = 2 <;> simp [src, hi'] at h
      · simp [src] at h
      · simp [src] at h
      · simp [src] at h
    · -- src = precommit-binding answer, read by the attempt binding and seeds 0/1
      by_cases h : depS c' (src (E₁ := E₁) (E₂ := E₂) (.inr (.inr (.inl b))))
      · have h' : depS c' (.inr (qBind 0)) := by simpa [src, hb] using h
        rcases rd_bind0 c' h' with ⟨b', hb', rfl⟩ | ⟨i', hi', rfl⟩
        · exact absurd (show b = b' from Fin.ext (by omega)) (fun e => hne (by rw [e]; rfl))
        · refine Or.inr (Or.inl ?_)
          simp only [depS, hb, if_false, src, qSeed, hi']
          simp
      · exact Or.inl h
  · by_cases hi : i.val = 2
    · refine Or.inl (fun h => ?_)
      have h' : depS c' (.inr (qSeed 1)) := by simpa [src, hi] using h
      rcases rd_seed c' 1 h' with ⟨h0, _⟩ | ⟨h2, _⟩ | ⟨_, i', hi', rfl⟩
      · exact absurd h0 (by decide)
      · exact absurd h2 (by decide)
      · exact hne (by rw [show i = i' from Fin.ext (by omega)]; rfl)
    · by_cases h : depS c' (src (E₁ := E₁) (E₂ := E₂) (.inr (.inr (.inr (.inl i)))))
      · have h' : depS c' (.inl 1) := by simpa [src, hi] using h
        rcases rd_sec c' 1 h' with ⟨h0, _⟩ | ⟨_, i', hi', rfl⟩ | ⟨h1, _⟩
        · exact absurd h0 (by decide)
        · have hii : i ≠ i' := fun e => hne (by rw [e]; rfl)
          refine Or.inr (Or.inr (fun pub vtag lv sec d rest => ?_))
          have hv : (i.val = 0 ∧ i'.val = 1) ∨ (i.val = 1 ∧ i'.val = 0) := by
            have := fun e => hii (Fin.ext e)
            omega
          rcases hv with ⟨h0, h1⟩ | ⟨h1, h0⟩
          · rw [show i = 0 from Fin.ext h0, show i' = 1 from Fin.ext h1]
            exact sep_seed pub vtag lv sec d rest
          · rw [show i = 1 from Fin.ext h1, show i' = 0 from Fin.ext h0]
            exact fun e => sep_seed pub vtag lv sec d rest e.symm
        · exact absurd h1 (by decide)
      · exact Or.inl h
  · by_cases h : depS c' (.inl 2)
    · rcases rd_sec c' 2 h with ⟨h0, _⟩ | ⟨h2, _⟩ | ⟨_, T', u', rfl⟩
      · exact absurd h0 (by decide)
      · exact absurd h2 (by decide)
      · refine Or.inr (Or.inr (fun pub vtag lv sec d rest => sep_salt pub vtag lv sec d rest T T' u u'
          (fun e => hne (by rw [e]; rfl))))
    · exact Or.inl h
  · exact Or.inl (fun h => hne (rd_salt c' T u h).symm)
  · exact Or.inl (fun h => hne (rd_childQ c' T n 1 h).symm)

end Pairs

/-! ### Opened reads -/

/-- The opened reads for opened fibres `fib`: the three roots, the opened
leaves and every node on their paths. -/
def openedQ (fib : Fin 3 → Finset Fib) : Fin 3 ⊕ RIdx → Prop
  | .inl _ => True
  | .inr (.inr (.inr (.inr (.inl (T, u))))) => u ∈ fib T
  | .inr (.inr (.inr (.inr (.inr (T, n))))) => ∃ u ∈ fib T, u.val / 2 ^ (n.1.val + 1) = n.2.val
  | _ => False

section Opened
variable {E₁ E₂ : ℕ}

def openedC (fib : Fin 3 → Finset Fib) : CPos E₁ E₂ → Prop
  | .inl _ => True
  | .inr (.inl _) => False
  | .inr (.inr q) => openedQ fib (.inr q)

theorem openedC_cposOf (fib : Fin 3 → Finset Fib) (c : Fin 3 ⊕ RIdx) :
    openedC (E₁ := E₁) (E₂ := E₂) fib (cposOf c) ↔ openedQ fib c := by
  rcases c with _ | _ <;> rfl

theorem div_pow_succ (u e : ℕ) : u / 2 ^ (e + 1 + 1) = u / 2 ^ (e + 1) / 2 := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- The designated field of an unopened read is neither read by nor the
answer of any opened read. -/
theorem hidden (fib : Fin 3 → Finset Fib) (c : Fin 3 ⊕ RIdx) (hc : openedQ fib c)
    (p : CPos E₁ E₂) (hp : ¬ openedC fib p) (q : RIdx) (hq : src p = .inr q) :
    ¬ depS (cposOf (E₁ := E₁) (E₂ := E₂) c) (.inr q) ∧ c ≠ .inr q := by
  have hcC : openedC (E₁ := E₁) (E₂ := E₂) fib (cposOf c) := (openedC_cposOf fib c).mpr hc
  rcases p with T | (c0 | c0) | (b | i | ⟨T, u⟩ | ⟨T, u⟩ | ⟨T, n⟩)
  · exact absurd trivial hp
  · simp only [src, Sum.inr.injEq] at hq
    subst hq
    refine ⟨fun h => ?_, fun e => by rw [e] at hc; simp [openedQ, qSeed] at hc⟩
    rcases rd_seed _ 0 h with ⟨_, c1, e⟩ | ⟨h2, _⟩ | ⟨h1, _⟩
    · rw [e] at hcC
      exact hcC
    · exact absurd h2 (by decide)
    · exact absurd h1 (by decide)
  · simp only [src, Sum.inr.injEq] at hq
    subst hq
    refine ⟨fun h => ?_, fun e => by rw [e] at hc; simp [openedQ, qSeed] at hc⟩
    rcases rd_seed _ 2 h with ⟨h0, _⟩ | ⟨_, c1, e⟩ | ⟨h1, _⟩
    · exact absurd h0 (by decide)
    · rw [e] at hcC
      exact hcC
    · exact absurd h1 (by decide)
  · by_cases hb : b.val = 0
    · simp [src, hb] at hq
    · simp only [src, hb, if_false, Sum.inr.injEq] at hq
      subst hq
      refine ⟨fun h => ?_, fun e => by rw [e] at hc; simp [openedQ, qBind] at hc⟩
      rcases rd_bind0 _ h with ⟨b', _, e⟩ | ⟨i', _, e⟩
      · rw [e] at hcC
        simp [openedC, openedQ, qBind] at hcC
      · rw [e] at hcC
        simp [openedC, openedQ, qSeed] at hcC
  · by_cases hi : i.val = 2
    · simp only [src, hi, if_true, Sum.inr.injEq] at hq
      subst hq
      refine ⟨fun h => ?_, fun e => by rw [e] at hc; simp [openedQ, qSeed] at hc⟩
      rcases rd_seed _ 1 h with ⟨h0, _⟩ | ⟨h2, _⟩ | ⟨_, i', _, e⟩
      · exact absurd h0 (by decide)
      · exact absurd h2 (by decide)
      · rw [e] at hcC
        simp [openedC, openedQ, qSeed] at hcC
    · simp [src, hi] at hq
  · simp [src] at hq
  · simp only [src, Sum.inr.injEq] at hq
    subst hq
    refine ⟨fun h => ?_, fun e => by rw [e] at hc; simp [openedQ, qSalt] at hc⟩
    have e := rd_salt _ T u h
    rw [e] at hcC
    exact hp hcC
  · simp only [src, Sum.inr.injEq] at hq
    subst hq
    refine ⟨fun h => ?_, fun e => ?_⟩
    · have e := rd_childQ _ T n 1 h
      rw [e] at hcC
      exact hp hcC
    · rw [e] at hc
      apply hp
      show ∃ u ∈ fib T, u.val / 2 ^ (n.1.val + 1) = n.2.val
      rcases childQ_cases T n 1 with ⟨h0, v, hv, ec⟩ | ⟨m, h1, h2, ec⟩
      · rw [ec] at hc
        simp only [openedQ, qLeaf] at hc
        refine ⟨v, hc, ?_⟩
        have e8 : (2 : ℕ) ^ (n.1.val + 1) = 2 := by rw [h0]; norm_num
        rw [e8, hv]
        omega
      · rw [ec] at hc
        simp only [openedQ, qNode] at hc
        obtain ⟨w, hw, hwm⟩ := hc
        refine ⟨w, hw, ?_⟩
        have e8 : (2 : ℕ) ^ (n.1.val + 1) = 2 ^ (m.1.val + 1 + 1) := by rw [h1]
        rw [e8, div_pow_succ, hwm, h2]
        omega

end Opened

#print axioms rd_rootChild
#print axioms rd_childQ
#print axioms rd_salt
#print axioms rd_seed
#print axioms rd_bind0
#print axioms rd_sec
#print axioms fresh_or_sep
#print axioms openedC_cposOf
#print axioms hidden
#print axioms div_pow_succ
end R1Z.LayoutR1PBin
