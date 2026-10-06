import FS.LemmaA
import FS.LemmaB

/-! # Composition: the §4 theorem

Lemma B puts the target event inside (collision) ∪ (Lemma A's event with the
(D2) bad sets).  Each (D2) bad set has density at most `max_i ε_i` over the
fresh block; Lemma A with `N = Q_tot` and (INJ)'s mass bound give §4. -/
set_option autoImplicit false
namespace FS

open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment

/-! ## `max_i ε_i` -/

theorem foldr_max_nonneg (ε : Nat → ℚ) : ∀ l : List Nat,
    0 ≤ l.foldr (fun i m => max (ε i) m) 0
  | [] => le_refl 0
  | _ :: l => le_max_of_le_right (foldr_max_nonneg ε l)

theorem le_foldr_max (ε : Nat → ℚ) : ∀ (l : List Nat) (i : Nat), i ∈ l →
    ε i ≤ l.foldr (fun i m => max (ε i) m) 0
  | [], i, h => by simp at h
  | a :: l, i, h => by
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact le_max_left _ _
      · exact le_max_of_le_right (le_foldr_max ε l i h)

theorem maxErr_nonneg (ε : Nat → ℚ) (r : Nat) : 0 ≤ maxErr ε r :=
  foldr_max_nonneg ε _

theorem le_maxErr (ε : Nat → ℚ) (r i : Nat) (h : i < r) : ε i ≤ maxErr ε r :=
  le_foldr_max ε _ i (List.mem_range.mpr h)

/-! ## Density over a block equals density over its first `k` answers -/

theorem mean_restrict {B : Type} [Fintype B] [Nonempty B] {K k : Nat} (h : k ≤ K)
    (g : (Fin k → B) → ℚ) :
    mean (fun b : Block B K => g (restrict h b)) = mean g := by
  have hK : k + (K - k) = K := Nat.add_sub_cancel' h
  let e : (Fin k ⊕ Fin (K - k)) ≃ Fin K := finSumFinEquiv.trans (finCongr hK)
  let E : ((Fin k → B) × (Fin (K - k) → B)) ≃ (Fin K → B) :=
    (Equiv.sumArrowEquivProdArrow (Fin k) (Fin (K - k)) B).symm.trans
      (Equiv.arrowCongr e (Equiv.refl B))
  have hE : ∀ pq : (Fin k → B) × (Fin (K - k) → B), restrict h (E pq) = pq.1 := by
    intro pq
    funext j
    have hj : e.symm (Fin.castLE h j) = Sum.inl j := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      simp [e]
    simp only [restrict, E, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
      Function.comp_apply, id_eq, hj]
    rfl
  rw [← mean_equiv E (fun b => g (restrict h b))]
  simp only [hE]
  rw [mean_prod (fun p _ => g p)]
  exact mean_congr fun p => mean_const (g p)

/-! ## Density of the (D2) bad sets -/

section Density
variable {X M C W Pf I B : Type} {K : Nat} [DecidableEq I] [Fintype I] [Fintype B] [Nonempty B]

omit [DecidableEq I] [Fintype I] in
theorem d2Bad_density (pr : Protocol X M C W Pf I B K) (rb : RoundByRound X M C I B K)
    (hD2 : D2 pr rb) (a : I) (T : Table I (Block B K)) :
    mean (fun b : Block B K => indicator (d2Bad pr rb a T b)) ≤ maxErr rb.ε pr.r := by
  classical
  by_cases hdec : ∃ (P : Prefix X M C) (m : M), pr.decode a T = some (P, m) ∧
      P.round < pr.r ∧ ∃ T', rb.doomed P T'
  · obtain ⟨P, m, hPm, hr, T', hT'⟩ := hdec
    have hiff : ∀ b : Block B K, d2Bad pr rb a T b ↔
        ¬ rb.doomed (P.ext m (pr.chal P.round b)) T := by
      intro b
      constructor
      · rintro ⟨P', m', hPm', _, _, hnot⟩
        rw [hPm] at hPm'
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hPm')
        exact hnot
      · intro hnot
        exact ⟨P, m, hPm, hr, ⟨T', hT'⟩, hnot⟩
    calc mean (fun b : Block B K => indicator (d2Bad pr rb a T b))
        = mean (fun b : Block B K =>
            indicator (¬ rb.doomed (P.ext m (pr.sampler P.round (restrict (pr.hk P.round) b))) T)) :=
          mean_congr fun b => indicator_iff (hiff b)
      _ = mean (fun t : Fin (pr.k P.round) → B =>
            indicator (¬ rb.doomed (P.ext m (pr.sampler P.round t)) T)) :=
          mean_restrict (pr.hk P.round)
            (fun t => indicator (¬ rb.doomed (P.ext m (pr.sampler P.round t)) T))
      _ ≤ rb.ε P.round := hD2 P.round P m T' T rfl hr hT'
      _ ≤ maxErr rb.ε pr.r := le_maxErr rb.ε pr.r P.round hr
  · have hzero : ∀ b : Block B K, indicator (d2Bad pr rb a T b) = 0 := by
      intro b
      rw [indicator_iff (q := False)]
      · exact indicator_false
      · constructor
        · rintro ⟨P, m, hPm, hr, hT', _⟩
          exact hdec ⟨P, m, hPm, hr, hT'⟩
        · exact False.elim
    rw [mean_congr hzero, mean_const]
    exact maxErr_nonneg rb.ε pr.r

end Density

/-! ## `Q_tot` on traces bounds first reads along every path -/

section Bridge
variable {I A O : Type} [DecidableEq I] [Nonempty A]

theorem firstReadsBound_of_traces (p : Program I A O) :
    ∀ (t : Table I A) (N : Nat),
      (∀ H : I → A, firstReads t (eval (complete t H) p).1 ≤ N) →
      FirstReadsBound p t N := by
  induction p with
  | done o => intros; trivial
  | ask i next ih =>
      intro t N hN
      cases ht : t i with
      | some a =>
          simp only [FirstReadsBound, ht]
          apply ih a t N
          intro H
          have := hN H
          simp only [eval, complete_cached t H i a ht, firstReads, ht, put_self t i a ht] at this
          simpa using this
      | none =>
          simp only [FirstReadsBound, ht]
          have hone : ∀ H : I → A, 1 + firstReads (put t i (H i)) (eval (complete t H) (next (H i))).1 ≤ N := by
            intro H
            have := hN H
            simpa [eval, complete_missing t H i ht, firstReads, ht] using this
          refine ⟨?_, ?_⟩
          · obtain ⟨a⟩ := (inferInstance : Nonempty A)
            have := hone (fun _ => a)
            omega
          · intro a
            apply ih a (put t i a) (N - 1)
            intro H
            have := hone (Function.update H i a)
            simp only [Function.update_self] at this
            rw [complete_resample t H i a ht] at this
            omega

end Bridge

/-! ## §4 -/

section Main
variable {X M C W Pf I B : Type} {K : Nat} [DecidableEq I] [Fintype I] [Fintype B] [Nonempty B]

theorem theorem4 (pr : Protocol X M C W Pf I B K) (rb : RoundByRound X M C I B K)
    (P : Program I (Block B K) Pf) (V : X → Pf → Program I (Block B K) Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : Theorem4 pr rb P V x κ Qtot := by
  intro hD1 hD2 hD3 hV inj hQ
  set exp := experiment P V x with hexp
  -- pointwise: target ⊆ collision ∪ Lemma A's event
  have hpoint : ∀ H : I → Block B K,
      indicator (accepts (eval H exp) ∧ extractFails pr x (eval H exp)) ≤
        indicator (inj.Coll (eval H exp)) +
          indicator (hitsBad (d2Bad pr rb) emptyTable (eval H exp).1) := by
    intro H
    refine le_trans (indicator_mono ?_) (indicator_or_le _ _)
    rintro ⟨hacc, hfail⟩
    by_cases hc : inj.Coll (eval H exp)
    · exact Or.inl hc
    · exact Or.inr (lemmaB pr rb P V x κ Qtot hD1 hD3 hV inj H hc hacc hfail)
  -- Lemma A's event: oracle law, then the union bound with N = Q_tot
  have hA : mean (fun H : I → Block B K =>
      indicator (hitsBad (d2Bad pr rb) emptyTable (eval H exp).1)) ≤ (Qtot : ℚ) * maxErr rb.ε pr.r := by
    rw [empty_oracle_law exp (fun v => indicator (hitsBad (d2Bad pr rb) emptyTable v.1))]
    apply lemmaA exp emptyTable Qtot (d2Bad pr rb) (maxErr rb.ε pr.r) (maxErr_nonneg _ _)
      (fun a T => d2Bad_density pr rb hD2 a T)
    apply firstReadsBound_of_traces
    intro H
    have := hQ H
    have hc : complete (emptyTable : Table I (Block B K)) H = H := rfl
    rw [hc]
    exact this
  calc mean (fun H : I → Block B K =>
          indicator (accepts (eval H exp) ∧ extractFails pr x (eval H exp)))
      ≤ mean (fun H : I → Block B K =>
          indicator (inj.Coll (eval H exp)) +
            indicator (hitsBad (d2Bad pr rb) emptyTable (eval H exp).1)) := mean_mono hpoint
    _ = mean (fun H : I → Block B K => indicator (inj.Coll (eval H exp))) +
          mean (fun H : I → Block B K =>
            indicator (hitsBad (d2Bad pr rb) emptyTable (eval H exp).1)) := mean_add _ _
    _ ≤ κ Qtot + (Qtot : ℚ) * maxErr rb.ε pr.r := add_le_add inj.mass hA
    _ = (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot := add_comm _ _

#print axioms theorem4
#print axioms lemmaA
#print axioms lemmaB
end Main
end FS
