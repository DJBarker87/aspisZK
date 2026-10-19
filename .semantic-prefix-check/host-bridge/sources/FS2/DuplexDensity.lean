import FS2.DuplexDecode

/-! # Chain density of the duplex decoder from (D2′)

The completing sampler reads the fresh absorbed state, then the round's two
cells and the late challenge cells in any order.  Its law is invariant under
permuting the cells (`listMean_perm`), so the late cells can be averaged
outside (`listMean_late_bound`); for each fixed completion the round's own
two cells carry exactly the law of `samp` on fresh answers, to which (D2′)
applies. -/
set_option autoImplicit false
namespace FS2.Duplex

open FS FS2 AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open scoped BigOperators
noncomputable section

section Perm
variable {I A C : Type} [DecidableEq I] [Inhabited A] [Fintype A] [Nonempty A]

/-- The multi-cell law is invariant under permuting the cells. -/
theorem listMean_perm (bad : C → Prop) {cells cells' : List I} (h : cells.Perm cells') :
    ∀ f : (I → A) → Program I A C, listMean bad cells f = listMean bad cells' f := by
  induction h with
  | nil => intro f; rfl
  | cons x _ ih =>
      intro f
      rw [listMean_cons, listMean_cons]
      exact mean_congr fun a => ih _
  | swap x y l =>
      intro f
      simp only [listMean_cons]
      by_cases hxy : x = y
      · subst hxy
        rfl
      · rw [mean_comm]
        apply mean_congr; intro a; apply mean_congr; intro b
        congr 1
        funext acc
        rw [Function.update_comm hxy]
  | trans _ _ ih1 ih2 => intro f; rw [ih1, ih2]

/-- Averaging the late cells outside: if for every completion `acc` the
round's two cells give mass at most `B`, so does the whole list. -/
theorem listMean_late_bound (bad : C → Prop) (c1 c2 : I) (hne : c1 ≠ c2)
    (G : (I → A) → C) (B : ℚ)
    (hg : ∀ acc : I → A, mean (fun a => mean (fun b =>
      indicator (bad (G (Function.update (Function.update acc c2 b) c1 a))))) ≤ B) :
    ∀ (ms : List I), (∀ c ∈ ms, c ≠ c1 ∧ c ≠ c2) →
      listMean bad (ms ++ [c1, c2]) (fun acc => .done (G acc)) ≤ B := by
  intro ms
  induction ms generalizing G with
  | nil =>
      intro _
      simp only [List.nil_append, listMean, multiProg, independentMean]
      exact hg default
  | cons c ms ih =>
      intro h
      have hc := h c (List.mem_cons_self ..)
      rw [List.cons_append, listMean_cons]
      calc mean (fun x => listMean bad (ms ++ [c1, c2])
            (fun acc => (fun acc => Program.done (G acc)) (Function.update acc c x)))
          ≤ mean (fun _ : A => B) := by
            apply mean_mono
            intro x
            apply ih (fun acc => G (Function.update acc c x))
            · intro acc
              have := hg (Function.update acc c x)
              have key : ∀ a b : A, Function.update (Function.update (Function.update acc c x) c2 b) c1 a =
                  Function.update (Function.update (Function.update acc c2 b) c1 a) c x := by
                intro a b
                rw [Function.update_comm hc.2, Function.update_comm hc.1]
              simp only [key] at this
              exact this
            · intro c' hc'
              exact h c' (List.mem_cons_of_mem _ hc')
        _ = B := mean_const B

/-- The two-cell law of `samp`'s continuation. -/
theorem listMean_two (bad : C → Prop) (c1 c2 : I) (hne : c1 ≠ c2) (g : A → A → C) :
    listMean bad [c1, c2] (fun acc => .done (g (acc c1) (acc c2))) =
      mean (fun a => mean (fun b => indicator (bad (g a b)))) := by
  simp only [listMean, multiProg, independentMean, Function.update_self,
    Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne)]

end Perm

variable {M Cv : Type} {L : Nat}

/-- The law of a round's sampler on fresh answers is the two-cell law. -/
theorem samp_mean {X : Type} (p : Params M Cv L) (i : Nat) (P : Prefix X M (Chal Cv)) (m : M)
    (bad : Chal Cv → Prop) :
    independentMean (samp p i P m).toProgram (fun w => indicator (bad w.2)) =
      mean (fun a => mean (fun b => indicator (bad (p.σ i a, b)))) := by
  have h1 : independentMean (samp p i P m).toProgram (fun w => indicator (bad w.2)) =
      mean (fun s' => independentMean (Sampler.multi (squeezeA p s') [advanceA p s']
        (by simp [squeezeA_ne_advanceA]) fun acc =>
          Sampler.done (p.σ i (acc (squeezeA p s')), acc (advanceA p s'))).toProgram
        (fun w => indicator (bad w.2))) := by
    unfold samp
    exact independentMean_ask _ _ bad
  have h2 : ∀ s' : State, independentMean (Sampler.multi (squeezeA p s') [advanceA p s']
        (by simp [squeezeA_ne_advanceA]) fun acc =>
          Sampler.done (p.σ i (acc (squeezeA p s')), acc (advanceA p s'))).toProgram
        (fun w => indicator (bad w.2)) =
      listMean bad [squeezeA p s', advanceA p s'] (fun acc =>
        Program.done (p.σ i (acc (squeezeA p s')), acc (advanceA p s'))) :=
    fun s' => independentMean_multi _ _ _ _ bad
  have h3 : ∀ s' : State, listMean bad [squeezeA p s', advanceA p s'] (fun acc =>
        Program.done (p.σ i (acc (squeezeA p s')), acc (advanceA p s'))) =
      mean (fun a => mean (fun b => indicator (bad (p.σ i a, b)))) :=
    fun s' => listMean_two bad (squeezeA p s') (advanceA p s') (squeezeA_ne_advanceA p s')
      (fun a b => (p.σ i a, b))
  rw [h1, mean_congr (fun s' => (h2 s').trans (h3 s'))]
  exact mean_const _

theorem chainDensity {X W Pf : Type} (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
    (extract : X → Table (Addr L) State → Option W)
    (rb : RoundByRound' X M (Chal Cv) (Addr L) State)
    (hD2 : FS2.D2 (protocol p x msg extract) rb) :
    ChainDensity (protocol p x msg extract) rb := by
  intro a T S hS
  change decode p x a T = some S at hS
  unfold decode at hS
  split at hS
  · cases hS
  rename_i s l data hparse
  split at hS
  · rename_i m recs hdec hwalk
    obtain rfl := Option.some.inj hS
    set pr := protocol p x msg extract with hpr
    have hr : pr.r = p.rounds := rfl
    -- the observer as a predicate on outputs
    let bad' : Prefix X M (Chal Cv) × M × Chal Cv → Prop := fun out =>
      d2Bad pr rb out.1 out.2.1 T out.2.2
    change independentMean _ (fun w => indicator (bad' w.2)) ≤ _
    rw [independentMean_ask]
    calc mean (fun s' => independentMean
            (if collides recs s' then
              (Sampler.done (⟨x, List.replicate p.rounds (m, (p.σ 0 s', s'))⟩, m, (p.σ 0 s', s')) :
                Sampler (Addr L) State (Prefix X M (Chal Cv) × M × Chal Cv))
            else Sampler.multi (squeezeA p s') (advanceA p s' :: missingCells p T recs s')
              (missingCells_nodup p T recs s') fun acc =>
                .done (completePrefix p x T recs acc, m,
                  (p.σ recs.length (acc (squeezeA p s')), acc (advanceA p s')))).toProgram
            (fun w => indicator (bad' w.2)))
        ≤ mean (fun _ : State => maxErr rb.ε pr.r) := by
          apply mean_mono
          intro s'
          by_cases hc : collides recs s'
          · rw [if_pos hc]
            simp only [Sampler.toProgram, independentMean]
            rw [indicator_iff (q := False), indicator_false]
            · exact maxErr_nonneg _ _
            · constructor
              · intro h
                have := h.1
                simp [Prefix.round, hr] at this
              · exact False.elim
          · rw [if_neg hc, independentMean_multi]
            have hperm : (squeezeA p s' :: advanceA p s' :: missingCells p T recs s').Perm
                (missingCells p T recs s' ++ [squeezeA p s', advanceA p s']) :=
              List.perm_append_comm (l₁ := [squeezeA p s', advanceA p s'])
            rw [listMean_perm bad' hperm]
            apply listMean_late_bound bad' (squeezeA p s') (advanceA p s') (squeezeA_ne_advanceA p s')
              (fun acc => (completePrefix p x T recs acc, m,
                (p.σ recs.length (acc (squeezeA p s')), acc (advanceA p s'))))
            · intro acc
              have hns : ∀ r ∈ recs, squeezeA p r.2.1 ≠ squeezeA p s' := by
                intro r hr' h
                apply hc
                rw [collides, List.mem_map]
                exact ⟨r, hr', squeezeA_injective p h⟩
              have hna : ∀ r ∈ recs, squeezeA p r.2.1 ≠ advanceA p s' := fun r _ h =>
                cross_disjoint _ _ (Addr.ofBytes_injective _ _ _ _ h)
              have hfix : ∀ a b : State, completePrefix p x T recs
                  (Function.update (Function.update acc (advanceA p s') b) (squeezeA p s') a) =
                  completePrefix p x T recs acc := by
                intro a b
                simp only [completePrefix]
                rw [completeRounds_update _ _ _ _ _ _ _ hns, completeRounds_update _ _ _ _ _ _ _ hna]
              simp only [Function.update_self,
                Function.update_of_ne (Ne.symm (squeezeA_ne_advanceA p s')), hfix]
              set P := completePrefix p x T recs acc with hP
              have hround : P.round = recs.length := completePrefix_round p x T recs acc
              by_cases hd : P.round < pr.r ∧ ∃ T', rb.doomed P T'
              · obtain ⟨hlt, T', hT'⟩ := hd
                have hiff : ∀ a b : State, bad' (P, m, (p.σ recs.length a, b)) ↔
                    ¬ rb.doomed (P.ext m (p.σ recs.length a, b)) T := by
                  intro a b
                  simp only [bad', d2Bad]
                  exact ⟨fun h => h.2.2, fun h => ⟨hlt, ⟨T', hT'⟩, h⟩⟩
                calc mean (fun a => mean (fun b => indicator (bad' (P, m, (p.σ recs.length a, b)))))
                    = mean (fun a => mean (fun b =>
                        indicator (¬ rb.doomed (P.ext m (p.σ recs.length a, b)) T))) := by
                      apply mean_congr; intro a; apply mean_congr; intro b
                      exact indicator_iff (hiff a b)
                  _ = independentMean (pr.samp recs.length P m).toProgram
                        (fun w => indicator (¬ rb.doomed (P.ext m w.2) T)) := by
                      rw [← samp_mean p recs.length P m (fun c => ¬ rb.doomed (P.ext m c) T)]
                      rfl
                  _ ≤ rb.ε recs.length := hD2 recs.length P m T' T hround (hround ▸ hlt) hT'
                  _ ≤ maxErr rb.ε pr.r := le_maxErr rb.ε pr.r recs.length (hround ▸ hlt)
              · have hz : ∀ a b : State, ¬ bad' (P, m, (p.σ recs.length a, b)) := by
                  intro a b h
                  exact hd ⟨h.1, h.2.1⟩
                rw [mean_congr (fun a => mean_congr (fun b =>
                  indicator_iff (iff_false_intro (hz a b))))]
                simp only [indicator_false]
                rw [mean_congr (fun a => mean_const (0 : ℚ)), mean_const]
                exact maxErr_nonneg _ _
            · intro c hcm
              rw [missingCells, List.mem_dedup, List.mem_filter] at hcm
              exact ⟨(decide_eq_true_iff.mp hcm.2).2.1, (decide_eq_true_iff.mp hcm.2).2.2⟩
      _ = maxErr rb.ε pr.r := mean_const _
  · cases hS

#print axioms chainDensity
end
end FS2.Duplex
