import FS2.DuplexWalk

/-! # `DecodesSpec` for the duplex with the chain-running verifier

Outside the collision event: `absC i` is first-read before `sqC i` and
`adC i` (their 32-byte prefix is its fresh output), and `adC i` before
`absC (i+1)` (whose prefix is its output); so every earlier round's cells
are in the table at `absC i`'s first read, the walk recovers the records, the
decoded completing sampler starts at `absC i`, and — all its cells being
fresh then and read later by the verifier — `follow` completes it to the
round's prefix, message and challenge. -/
set_option autoImplicit false
namespace FS2.Duplex

open FS FS2 AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section

variable {M Cv X W Pf : Type} {L : Nat}

/-! ## `traceFrom` -/

section TraceFrom
variable {I A : Type} [DecidableEq I]

theorem traceFrom_eq (H : I → A) : ∀ (tr : List (I × A)) (a : I), (∀ q ∈ tr, q.2 = H q.1) →
    Read tr a → ∃ rest, traceFrom tr a = (a, H a) :: rest ∧
      (∀ q ∈ rest, q.2 = H q.1) ∧ (∀ b, Read tr b → Before tr a b → b ∈ rest.map Prod.fst) := by
  intro tr
  induction tr with
  | nil => intro a _ h; simp [Read] at h
  | cons q rest ih =>
      intro a hcons ha
      obtain ⟨i, v⟩ := q
      have hv : v = H i := hcons (i, v) (List.mem_cons_self ..)
      have hrest : ∀ q ∈ rest, q.2 = H q.1 := fun q hq => hcons q (List.mem_cons_of_mem _ hq)
      by_cases hia : i = a
      · subst hia
        refine ⟨rest, by simp [traceFrom, hv], hrest, ?_⟩
        intro b hrb hB
        obtain ⟨_, hlt⟩ := hB
        have hib : i ≠ b := by
          intro e; subst e; exact lt_irrefl _ hlt
        have hrb' : b ∈ i :: rest.map Prod.fst := hrb
        rcases List.mem_cons.mp hrb' with h | h
        · exact absurd h.symm hib
        · exact h
      · have ha' : Read rest a := by
          have ha'' : a ∈ i :: rest.map Prod.fst := ha
          rcases List.mem_cons.mp ha'' with h | h
          · exact absurd h.symm hia
          · exact h
        obtain ⟨r, hr, hc, hb⟩ := ih a hrest ha'
        refine ⟨r, by simp [traceFrom, hia, hr], hc, ?_⟩
        intro b hrb hB
        obtain ⟨_, hlt⟩ := hB
        have hib : i ≠ b := by
          intro e; subst e
          simp [firstIdx, hia] at hlt
        have hrb2 : Read rest b := by
          have hrb' : b ∈ i :: rest.map Prod.fst := hrb
          rcases List.mem_cons.mp hrb' with h | h
          · exact absurd h.symm hib
          · exact h
        apply hb b hrb2
        refine ⟨ha', ?_⟩
        simp only [firstIdx, hia, hib, if_false] at hlt
        omega

end TraceFrom

/-! ## Ordering of the transcript's cells -/

section Order
variable (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
  (extract : X → Table (Addr L) State → Option W) (H : Addr L → State) (π : Pf)
  (tr : List (Addr L × State)) (hcons : ∀ q ∈ tr, q.2 = H q.1) (Qtot : Nat)
  (hQ : firstReads emptyTable tr ≤ Qtot) (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
  (r : Nat)
  (hread : ∀ j < r, Read tr (absC p x msg extract H π j) ∧ Read tr (sqC p x msg extract H π j) ∧
    Read tr (adC p x msg extract H π j))

include hcons hQ hcoll hread

theorem abs_before_sq (i : Nat) (hi : i < r) :
    Before tr (absC p x msg extract H π i) (sqC p x msg extract H π i) :=
  noColl_prefix_after p Qtot H tr hcons hQ hcoll _ _ (hread i hi).1 (hread i hi).2.1 (toBytes_squeezeA p _)

theorem abs_before_ad (i : Nat) (hi : i < r) :
    Before tr (absC p x msg extract H π i) (adC p x msg extract H π i) :=
  noColl_prefix_after p Qtot H tr hcons hQ hcoll _ _ (hread i hi).1 (hread i hi).2.2 (toBytes_advanceA p _)

theorem ad_before_abs (i : Nat) (hi : i + 1 < r) :
    Before tr (adC p x msg extract H π i) (absC p x msg extract H π (i + 1)) := by
  apply noColl_prefix_after p Qtot H tr hcons hQ hcoll _ _ (hread i (by omega)).2.2 (hread (i + 1) hi).1
  rw [absC, toBytes_absorbA, sv_succ]

theorem abs_before_abs : ∀ j i, j < i → i < r →
    Before tr (absC p x msg extract H π j) (absC p x msg extract H π i) := by
  intro j i hji hi
  induction i with
  | zero => omega
  | succ i ih =>
      have h1 := before_trans tr
        (abs_before_ad p x msg extract H π tr hcons Qtot hQ hcoll r hread i (by omega))
        (ad_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread i hi)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hji with h | h
      · exact before_trans tr (ih h (by omega)) h1
      · subst h; exact h1

theorem ad_before_abs' (j i : Nat) (hji : j < i) (hi : i < r) :
    Before tr (adC p x msg extract H π j) (absC p x msg extract H π i) := by
  rcases Nat.lt_iff_add_one_le.mp hji |>.lt_or_eq with h | h
  · exact before_trans tr
      (ad_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread j (by omega))
      (abs_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread _ _ h hi)
  · rw [← h]; exact ad_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread j (h ▸ hi)

/-- The absorbed states of distinct rounds differ. -/
theorem sv'_ne (j i : Nat) (hji : j < i) (hi : i < r) :
    sv' p x msg extract H π j ≠ sv' p x msg extract H π i := by
  apply noColl_injective p Qtot H tr hcons hQ hcoll _ _ (hread j (by omega)).1 (hread i hi).1
  exact before_ne tr (abs_before_abs p x msg extract H π tr hcons Qtot hQ hcoll r hread j i hji hi)

end Order


/-! ## The assembly -/

section Assembly
variable (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
  (extract : X → Table (Addr L) State → Option W)
  (decision : Prefix X M (Chal Cv) → M → Bool) (P : Program (Addr L) State Pf) (Qtot : Nat)

local notation "pr" => protocol p x msg extract
local notation "V" => verifier (protocol p x msg extract) decision

theorem decodesSpec (hQ : ∀ H, distinctFirstReads (eval H (experiment P (V) x)) ≤ Qtot) :
    DecodesSpec p x msg extract P (V) Qtot := by
  intro H hcoll i a hi
  dsimp only
  intro ha
  -- the execution
  set v := eval H (experiment P (V) x) with hv
  set tr := v.1 with htr
  have hπ : v.2.1 = (eval H P).2 := by rw [hv, experiment_eval]
  set π := (eval H P).2 with hπdef
  rw [hπ] at ha ⊢
  have hcons : ∀ q ∈ tr, q.2 = H q.1 := FS.eval_consistent H _
  have hQ' : firstReads emptyTable tr ≤ Qtot := hQ H
  have hcoll' : ¬ hitsBad (badColl p Qtot) emptyTable tr := hcoll
  have hr : (pr).r = p.rounds := rfl
  -- every chain cell of every round is read (by the verifier)
  have hread : ∀ j < p.rounds, Read tr (absC p x msg extract H π j) ∧
      Read tr (sqC p x msg extract H π j) ∧ Read tr (adC p x msg extract H π j) := by
    intro j hj
    have hV : ∀ c, c ∈ (eval H ((pr).chain H x π j).toProgram).1.map Prod.fst → Read tr c := by
      intro c hc
      have := verifier_reads (pr) decision H x π j hj c hc
      rw [htr, hv, experiment_eval]
      unfold Read
      simp only [List.map_append, List.mem_append]
      exact Or.inr this
    rw [chain_trace] at hV
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hV
    exact ⟨hV _ (Or.inl rfl), hV _ (Or.inr (Or.inl rfl)), hV _ (Or.inr (Or.inr rfl))⟩
  have hread2 : ∀ j < p.rounds, Read tr (absC p x msg extract H π j) ∧ Read tr (adC p x msg extract H π j) :=
    fun j hj => ⟨(hread j hj).1, (hread j hj).2.2⟩
  have ha' : a = absC p x msg extract H π i := by
    rw [firstCell_chain] at ha
    exact (Option.some.inj ha).symm
  subst ha'
  -- the table at the absorb's first read
  set T := tableBefore emptyTable tr (absC p x msg extract H π i) with hT
  have hT' : ∀ b w, T b = some w → w = H b ∧ Read tr b := by
    intro b w hbw
    rw [hT, tableBefore_eq H tr emptyTable _ b hcons] at hbw
    split at hbw
    · rename_i hB
      exact ⟨(Option.some.inj hbw).symm, hB.1⟩
    · cases hbw
  have hT_before : ∀ b, Before tr b (absC p x msg extract H π i) → T b ≠ none := by
    intro b hB
    rw [hT, tableBefore_eq H tr emptyTable _ b hcons, if_pos hB]
    exact Option.some_ne_none _
  have hT_none : ∀ b, ¬ Before tr b (absC p x msg extract H π i) → T b = none := by
    intro b hB
    rw [hT, tableBefore_eq H tr emptyTable _ b hcons, if_neg hB]; rfl
  have hcells : ∀ j < i, T (adC p x msg extract H π j) ≠ none ∧ T (absC p x msg extract H π j) ≠ none := by
    intro j hj
    exact ⟨hT_before _ (ad_before_abs' p x msg extract H π tr hcons Qtot hQ' hcoll' p.rounds hread j i hj hi),
      hT_before _ (abs_before_abs p x msg extract H π tr hcons Qtot hQ' hcoll' p.rounds hread j i hj hi)⟩
  have hwalk := walk_eq p x msg extract H π tr hcons Qtot hQ' hcoll' p.rounds hread2 i p.rounds
    (le_of_lt hi) (le_of_lt hi) T hT' hcells
  -- the decoded sampler
  have hcollide : ¬ collides (recs p x msg extract H π i) (sv' p x msg extract H π i) := by
    intro hc
    rw [collides, recs_eq, List.map_map, List.mem_map] at hc
    obtain ⟨j, hj, hje⟩ := hc
    rw [List.mem_range] at hj
    exact sv'_ne p x msg extract H π tr hcons Qtot hQ' hcoll' p.rounds hread j i hj hi hje
  have hdec : (pr).decode (absC p x msg extract H π i) T =
      some (.ask (absC p x msg extract H π i) fun s' =>
        if collides (recs p x msg extract H π i) s' then
          .done (⟨x, List.replicate p.rounds (msg π i, (p.σ 0 s', s'))⟩, msg π i, (p.σ 0 s', s'))
        else
          .multi (squeezeA p s') (advanceA p s' :: missingCells p T (recs p x msg extract H π i) s')
            (missingCells_nodup p T (recs p x msg extract H π i) s') fun acc =>
              .done (completePrefix p x T (recs p x msg extract H π i) acc, msg π i,
                (p.σ (recs p x msg extract H π i).length (acc (squeezeA p s')),
                  acc (advanceA p s')))) := by
    simp only [protocol, decode, parseAbsorb_absC, p.decEnc, hwalk]
  refine ⟨_, hdec, ?_⟩
  · -- follow the sampler from the absorb's first read
    obtain ⟨rest, hrest, hrcons, hmem⟩ := traceFrom_eq H tr _ hcons (hread i hi).1
    rw [hrest]
    change follow (Sampler.ask _ _) T ((absC p x msg extract H π i, sv' p x msg extract H π i) :: rest) = _
    simp only [follow, if_true]
    rw [hT, tableBefore_self H tr _ hcons]
    simp only [if_true]
    rw [if_neg hcollide]
    have hfresh : ∀ c ∈ squeezeA p (sv' p x msg extract H π i) ::
        advanceA p (sv' p x msg extract H π i) :: missingCells p T (recs p x msg extract H π i)
          (sv' p x msg extract H π i),
        (put T (absC p x msg extract H π i) (sv' p x msg extract H π i)) c = none ∧
          c ∈ rest.map Prod.fst := by
      intro c hc
      have hsq := abs_before_sq p x msg extract H π tr hcons Qtot hQ' hcoll' p.rounds hread i hi
      have had := abs_before_ad p x msg extract H π tr hcons Qtot hQ' hcoll' p.rounds hread i hi
      have hne1 : ∀ s, squeezeA p s ≠ absC p x msg extract H π i := by
        intro s; unfold absC; exact squeezeA_ne_absorbA p _ _ _ _ _
      have hne2 : ∀ s, advanceA p s ≠ absC p x msg extract H π i := by
        intro s; unfold absC; exact advanceA_ne_absorbA p _ _ _ _ _
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · refine ⟨?_, hmem _ (hread i hi).2.1 hsq⟩
        rw [put, if_neg (hne1 _)]
        apply hT_none
        intro h
        exact lt_asymm hsq.2 h.2
      · refine ⟨?_, hmem _ (hread i hi).2.2 had⟩
        rw [put, if_neg (hne2 _)]
        apply hT_none
        intro h
        exact lt_asymm had.2 h.2
      · rw [missingCells, List.mem_dedup, List.mem_filter, List.mem_map] at hc
        obtain ⟨⟨r', hr', rfl⟩, hfilt⟩ := hc
        have hfilt' := decide_eq_true_iff.mp hfilt
        rw [recs_eq, List.mem_map] at hr'
        obtain ⟨j, hj, rfl⟩ := hr'
        rw [List.mem_range] at hj
        dsimp only at hfilt' ⊢
        refine ⟨?_, ?_⟩
        · rw [put, if_neg (hne1 _)]
          exact hfilt'.1
        · apply hmem _ (hread j (by omega)).2.1
          rcases before_total tr _ _ (hread i hi).1 (hread j (by omega)).2.1
            (Ne.symm (hne1 _)) with h | h
          · exact h
          · exact absurd hfilt'.1 (hT_before _ h)
    rw [← hT]
    rw [follow_multi_complete H rest _ _ _ _ _ hrcons hfresh]
    -- the output is the round's prefix, message and challenge
    congr 1
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · set acc := accOf H (squeezeA p (sv' p x msg extract H π i) ::
        advanceA p (sv' p x msg extract H π i) ::
          missingCells p T (recs p x msg extract H π i) (sv' p x msg extract H π i)) default with hacc
      show completePrefix p x T (recs p x msg extract H π i) acc = (pr).transcript H x π i
      have hstmt := transcript_statement p x msg extract H π i
      have hrounds : completeRounds p T acc 0 (recs p x msg extract H π i) =
          ((pr).transcript H x π i).rounds := by
        apply completeRounds_recs
        intro j hj
        cases hTj : T (sqC p x msg extract H π j) with
        | some w => simp only [Option.getD_some]; exact (hT' _ _ hTj).1
        | none =>
            simp only [Option.getD_none]
            rw [hacc, accOf_apply]
            have hmemc : sqC p x msg extract H π j ∈ squeezeA p (sv' p x msg extract H π i) ::
                advanceA p (sv' p x msg extract H π i) ::
                  missingCells p T (recs p x msg extract H π i) (sv' p x msg extract H π i) := by
              right; right
              unfold missingCells
              apply List.mem_dedup.mpr
              apply List.mem_filter.mpr
              refine ⟨?_, ?_⟩
              · apply List.mem_map.mpr
                refine ⟨(sv p x msg extract H π j, sv' p x msg extract H π j, msg π j,
                  H (adC p x msg extract H π j)), ?_, rfl⟩
                rw [recs_eq]
                exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
              · apply decide_eq_true_iff.mpr
                refine ⟨hTj, ?_, ?_⟩
                · intro e
                  exact sv'_ne p x msg extract H π tr hcons Qtot hQ' hcoll' p.rounds hread j i hj hi
                    (squeezeA_injective p e)
                · exact squeezeA_ne_advanceA' p _ _
            rw [if_pos hmemc]
      cases h : (pr).transcript H x π i with
      | mk st rs =>
          simp only [completePrefix]
          rw [h] at hstmt hrounds
          simp only at hstmt hrounds
          rw [hstmt, hrounds]
    · show (p.σ (recs p x msg extract H π i).length _, _) = (pr).chal H x π i
      rw [recs_length, chal_eq, accOf_apply, accOf_apply]
      simp only [List.mem_cons, true_or, or_true, if_true, Prod.mk.injEq]
      try exact ⟨rfl, rfl⟩

/-- A chain's first cell is in its own trace (any transcript statement). -/
theorem firstCell_mem_chain (x' : X) (H : Addr L → State) (π : Pf) (j : Nat) (a : Addr L)
    (ha : firstCell ((pr).chain H x' π j) = some a) :
    a ∈ (eval H ((pr).chain H x' π j).toProgram).1.map Prod.fst := by
  change firstCell (samp p j _ _) = some a at ha
  change a ∈ (eval H (samp p j _ _).toProgram).1.map Prod.fst
  simp only [samp, firstCell, Option.some.injEq] at ha
  subst ha
  simp [samp, Sampler.toProgram, eval, multiProg]

/-- The duplex Fiat–Shamir bound with the chain-running verifier: no
remaining (INJ) obligation. -/
theorem duplex_fiat_shamir_verifier (rb : RoundByRound' X M (Chal Cv) (Addr L) State)
    (hD1 : FS2.D1 (pr) rb) (hD2 : FS2.D2 (pr) rb) (hD3 : FS2.D3 (pr) rb (V))
    (hQ : ∀ H, distinctFirstReads (eval H (experiment P (V) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
        indicator (accepts (eval H (experiment P (V) x)) ∧
          extractFails (pr) x (eval H (experiment P (V) x)))) ≤
      (Qtot : ℚ) * maxErr rb.ε p.rounds + κ Qtot :=
  duplex_fiat_shamir p x msg extract rb P (V) Qtot hD1 hD2 hD3
    (fun H x' π j a hj ha => verifier_reads (pr) decision H x' π j hj a
      (firstCell_mem_chain p x msg extract x' H π j a ha))
    hQ (decodesSpec p x msg extract decision P Qtot hQ)

#print axioms decodesSpec
#print axioms duplex_fiat_shamir_verifier
end Assembly

end
end FS2.Duplex
