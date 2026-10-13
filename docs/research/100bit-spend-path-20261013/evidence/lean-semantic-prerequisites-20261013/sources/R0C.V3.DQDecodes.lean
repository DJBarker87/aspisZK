import R0C.V3.DQChain

/-! # The q22 duplex decoder succeeds outside the collision event

For every round `i < 5` of the transcript, the decoder applied at the first
read of the round's absorb cell returns the round's completing sampler, and
it is followed to the round's prefix, message and challenge. -/
set_option autoImplicit false
namespace R0C.V3.DQ

open FS FS2 FS2.Duplex R0FS R0FS.V2 R0C.V3
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section

variable {Sfield : Fin 29 → Subfield E} {Pf : Type} {L : Nat}
variable (p : Duplex.Params (Msg E) (R0FS.Chal E) L) (x : Stmt E Sfield) (msg : Pf → Nat → Msg E)

local notation "prQ" => protocolQ (Sfield := Sfield) p x msg
local notation "prV" => Duplex.protocol p x msg (extr (Sfield := Sfield) (L := L))

theorem transcriptQ (H : Addr L → State) (π : Pf) :
    ∀ i, i ≤ 4 → (prQ).transcript H x π i = (prV).transcript H x π i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hi
      have h := ih (by omega)
      show ((prQ).transcript H x π i).ext (msg π i)
          (eval H ((prQ).samp i ((prQ).transcript H x π i) (msg π i)).toProgram).2 =
        ((prV).transcript H x π i).ext (msg π i)
          (eval H ((prV).samp i ((prV).transcript H x π i) (msg π i)).toProgram).2
      rw [h]
      have hs : (prQ).samp i ((prV).transcript H x π i) (msg π i) =
          (prV).samp i ((prV).transcript H x π i) (msg π i) := by
        show sampQ p i _ _ = Duplex.samp p i _ _
        simp only [sampQ, if_pos (show i < 4 by omega)]
      rw [hs]

theorem chalQ_lt (H : Addr L → State) (π : Pf) (i : Nat) (hi : i < 4) :
    (prQ).chal H x π i = (prV).chal H x π i := by
  show (eval H ((prQ).samp i ((prQ).transcript H x π i) (msg π i)).toProgram).2 =
    (eval H ((prV).samp i ((prV).transcript H x π i) (msg π i)).toProgram).2
  rw [transcriptQ p x msg H π i (by omega)]
  show (eval H (sampQ p i _ _).toProgram).2 = _
  simp only [sampQ, if_pos hi]
  rfl

theorem chainQ_lt (H : Addr L → State) (π : Pf) (i : Nat) (hi : i < 4) :
    (prQ).chain H x π i = (prV).chain H x π i := by
  show sampQ p i ((prQ).transcript H x π i) (msg π i) = Duplex.samp p i _ _
  rw [transcriptQ p x msg H π i (by omega)]
  simp only [sampQ, if_pos hi]
  rfl

theorem chainQ_4 (H : Addr L → State) (π : Pf) :
    (prQ).chain H x π 4 =
      .ask (absC p x msg (extr (Sfield := Sfield) (L := L)) H π 4) fun s' =>
        chainS p (out4 s') 8 s' [] [] := by
  show sampQ p 4 ((prQ).transcript H x π 4) (msg π 4) = _
  rw [transcriptQ p x msg H π 4 le_rfl]
  simp only [sampQ, show ¬ (4 < 4) from by omega, if_false]
  rfl

theorem firstCellQ (H : Addr L → State) (π : Pf) (i : Nat) (hi : i ≤ 4) :
    firstCell ((prQ).chain H x π i) = some (absC p x msg (extr (Sfield := Sfield) (L := L)) H π i) := by
  rcases Nat.lt_or_ge i 4 with h | h
  · rw [chainQ_lt p x msg H π i h]; exact firstCell_chain p x msg _ H π i
  · obtain rfl : i = 4 := by omega
    rw [chainQ_4]
    exact FS2.firstCell.eq_2 _ _

theorem eval_ask_out {C : Type} (H : Addr L → State) (a : Addr L) (k : State → FS2.Sampler (Addr L) State C) :
    (eval H (FS2.Sampler.ask a k).toProgram).2 = (eval H (k (H a)).toProgram).2 := rfl

theorem chalQ_4 (H : Addr L → State) (π : Pf) :
    (prQ).chal H x π 4 =
      out4 (sv' p x msg (extr (Sfield := Sfield) (L := L)) H π 4)
        ((List.range 8).map fun k => H (squeezeA p (st p H (sv' p x msg (extr (Sfield := Sfield) (L := L)) H π 4) k)))
        ((List.range 8).map fun k => st p H (sv' p x msg (extr (Sfield := Sfield) (L := L)) H π 4) (k + 1)) := by
  show (eval H ((prQ).chain H x π 4).toProgram).2 = _
  rw [chainQ_4, eval_ask_out, chainS_out]
  simp only [List.nil_append]
  rfl


/-! ## Helpers -/

theorem eval_ask_trace {C : Type} (H : Addr L → State) (a : Addr L) (k : State → FS2.Sampler (Addr L) State C) :
    (eval H (FS2.Sampler.ask a k).toProgram).1 = (a, H a) :: (eval H (k (H a)).toProgram).1 := rfl

theorem accFrom_map (H : Addr L → State) : ∀ (cells : List (Addr L)) (c : Addr L), c ∈ cells →
    accFrom cells (cells.map H) c = H c := by
  intro cells
  induction cells with
  | nil => intro c h; simp at h
  | cons d ds ih =>
      intro c hc
      unfold accFrom at ih ⊢
      by_cases hcd : c = d
      · subst hcd; simp [List.lookup]
      · have : c ∈ ds := (List.mem_cons.mp hc).resolve_left hcd
        have hb : (c == d) = false := by simpa using hcd
        simp only [List.map_cons, List.zip_cons_cons, List.lookup, hb]
        exact ih c this

theorem order_chain (H : Addr L → State) (tr : List (Addr L × State)) :
    ∀ (n : Nat) (s : State) (xs : List State),
      (∀ j k, j < k → k < n → Before tr (advanceA p (st p H s j)) (squeezeA p (st p H s k)) ∧
        Before tr (advanceA p (st p H s j)) (advanceA p (st p H s k))) →
      OrderOK tr (evs H (chainBS p n s xs)) := by
  intro n
  induction n with
  | zero => intro s xs _; trivial
  | succ n ih =>
      intro s xs h
      refine ⟨fun hb => absurd hb (by simp), fun _ e he => ?_, ih _ _ ?_⟩
      · obtain ⟨k, hk, he'⟩ := evs_chainBS_mem p H n _ _ e he
        have h' := h 0 (k + 1) (by omega) (by omega)
        rw [st_succ'] at h'
        rcases he' with rfl | rfl
        · exact h'.1
        · exact h'.2
      · intro j k hjk hk
        have h' := h (j + 1) (k + 1) (by omega) (by omega)
        rw [st_succ', st_succ'] at h'
        exact h'

theorem order_traceFrom (tr : List (Addr L × State)) (a : Addr L) (ha : Read tr a) :
    ∀ ev : List (Bool × Addr L), OrderOK tr ev → (∀ e ∈ ev, e.2 = a ∨ Before tr a e.2) →
      OrderOK (traceFrom tr a) ev := by
  intro ev
  induction ev with
  | nil => intro _ _; trivial
  | cons e es ih =>
      intro ho hc
      obtain ⟨b, c⟩ := e
      refine ⟨fun hb e he => before_traceFrom a c e.2 tr ha (hc (b, c) (List.mem_cons_self ..))
        (ho.1 hb e he), ih ho.2 fun e he => hc e (List.mem_cons_of_mem _ he)⟩

theorem chain_nodup (H : Addr L → State) : ∀ (n : Nat) (s : State) (xs : List State),
    (∀ j k, j < k → k < n → st p H s j ≠ st p H s k) →
    ((evs H (chainBS p n s xs)).map Prod.snd).Nodup := by
  intro n
  induction n with
  | zero => intro s xs _; simp [chainBS, evs]
  | succ n ih =>
      intro s xs h
      have hrest : ∀ c ∈ (evs H (chainBS p n (H (advanceA p s)) (xs ++ [H (advanceA p s)]))).map Prod.snd,
          ∃ k < n, c = squeezeA p (st p H s (k + 1)) ∨ c = advanceA p (st p H s (k + 1)) := by
        intro c hc
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
        obtain ⟨k, hk, he'⟩ := evs_chainBS_mem p H n _ _ e he
        refine ⟨k, hk, ?_⟩
        rw [st_succ']
        rcases he' with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      simp only [chainBS, evs, List.map_cons, List.nodup_cons, List.mem_cons, not_or]
      refine ⟨⟨squeezeA_ne_advanceA' p _ _, fun hm => ?_⟩, fun hm => ?_, ih _ _ ?_⟩
      · obtain ⟨k, hk, hc⟩ := hrest _ hm
        rcases hc with hc | hc
        · exact h 0 (k + 1) (by omega) (by omega) (squeezeA_injective p hc)
        · exact squeezeA_ne_advanceA' p _ _ hc
      · obtain ⟨k, hk, hc⟩ := hrest _ hm
        rcases hc with hc | hc
        · exact squeezeA_ne_advanceA' p _ _ hc.symm
        · exact h 0 (k + 1) (by omega) (by omega) (advanceA_injective p hc)
      · intro j k hjk hk
        have := h (j + 1) (k + 1) (by omega) (by omega)
        rwa [st_succ', st_succ'] at this


/-! ## The decoder succeeds -/

theorem waiting_none (cells : List (Addr L)) :
    waiting (cells.map fun c => ((c, none) : Addr L × Option State)) = cells := by
  induction cells with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, waiting, ih]

theorem decodesQ (hr5 : p.rounds = 5) (decision : Prefix (Stmt E Sfield) (Msg E) DC → Msg E → Bool)
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)) ≤ Qtot)
    (H : Addr L → State) (hcoll : ¬ Coll p Qtot (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)))
    (i : Nat) (a : Addr L) (hi : i < (prQ).r)
    (ha : firstCell ((prQ).chain H x (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)).2.1 i) = some a) :
    ∃ own pend g, decQ p x a (tableBefore emptyTable (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)).1 a) =
        some (own, pend, g) ∧
      bfollow g (traceFrom (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)).1 a) own pend
        (tableBefore emptyTable (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)).1 a) =
        some ((prQ).transcript H x (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)).2.1 i,
          (prQ).msg (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)).2.1 i,
          (prQ).chal H x (eval H (FS2.experiment P (FS2.verifier (prQ) decision) x)).2.1 i) := by
  set v := eval H (FS2.experiment P (FS2.verifier (prQ) decision) x) with hv
  have hπ : v.2.1 = (eval H P).2 := by rw [hv, FS2.experiment_eval]
  set π := (eval H P).2 with hπdef
  rw [hπ] at ha ⊢
  have hcons : ∀ q ∈ v.1, q.2 = H q.1 := FS.eval_consistent H _
  have hQ' : firstReads emptyTable v.1 ≤ Qtot := hQ H
  have hcoll' : ¬ hitsBad (badColl p Qtot) emptyTable v.1 := hcoll
  have hr : (prQ).r = 5 := hr5
  have hi4 : i ≤ 4 := by omega
  set ex := extr (Sfield := Sfield) (L := L) with hex
  -- every chain cell is read
  have hreadV : ∀ j < 5, ∀ c ∈ (eval H ((prQ).chain H x π j).toProgram).1.map Prod.fst, Read v.1 c := by
    intro j hj c hc
    have := FS2.verifier_reads (prQ) decision H x π j (by rw [hr]; exact hj) c hc
    show c ∈ v.1.map Prod.fst
    rw [hv, FS2.experiment_eval, List.map_append, List.mem_append]
    exact Or.inr this
  have hread4 : ∀ j < 4, Read v.1 (absC p x msg ex H π j) ∧ Read v.1 (sqC p x msg ex H π j) ∧
      Read v.1 (adC p x msg ex H π j) := by
    intro j hj
    have h := hreadV j (by omega)
    rw [chainQ_lt p x msg H π j hj, chain_trace] at h
    exact ⟨h _ (List.mem_cons_self ..), h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))⟩
  have habs4 : Read v.1 (absC p x msg ex H π 4) := by
    have h := hreadV 4 (by omega)
    rw [chainQ_4, eval_ask_trace] at h
    exact h _ (List.mem_cons_self ..)
  have hchain4 : ∀ k < 8, Read v.1 (squeezeA p (st p H (sv' p x msg ex H π 4) k)) ∧
      Read v.1 (advanceA p (st p H (sv' p x msg ex H π 4) k)) := by
    intro k hk
    have h := hreadV 4 (by omega)
    rw [chainQ_4, eval_ask_trace] at h
    obtain ⟨h1, h2⟩ := chainS_reads p H (out4 (H (absC p x msg ex H π 4))) 8
      (H (absC p x msg ex H π 4)) [] [] k hk
    exact ⟨h _ (List.mem_cons_of_mem _ h1), h _ (List.mem_cons_of_mem _ h2)⟩
  have hreadA : Read v.1 (absC p x msg ex H π i) := by
    rcases Nat.lt_or_ge i 4 with h | h
    · exact (hread4 i h).1
    · obtain rfl : i = 4 := by omega
      exact habs4
  -- the earlier rounds' cells precede this round's absorb
  have h34 : Before v.1 (adC p x msg ex H π 3) (absC p x msg ex H π 4) := by
    apply noColl_prefix_after p Qtot H v.1 hcons hQ' hcoll' _ _ (hread4 3 (by omega)).2.2 habs4
    rw [absC, toBytes_absorbA, sv_succ]
  have hB : ∀ j < i, Before v.1 (adC p x msg ex H π j) (absC p x msg ex H π i) ∧
      Before v.1 (absC p x msg ex H π j) (absC p x msg ex H π i) := by
    intro j hji
    rcases Nat.lt_or_ge i 4 with h | h
    · exact ⟨ad_before_abs' p x msg ex H π v.1 hcons Qtot hQ' hcoll' 4 hread4 j i hji h,
        abs_before_abs p x msg ex H π v.1 hcons Qtot hQ' hcoll' 4 hread4 j i hji h⟩
    · obtain rfl : i = 4 := by omega
      have h33 := abs_before_ad p x msg ex H π v.1 hcons Qtot hQ' hcoll' 4 hread4 3 (by omega)
      rcases Nat.lt_or_ge j 3 with hj | hj
      · exact ⟨before_trans v.1 (before_trans v.1
            (ad_before_abs' p x msg ex H π v.1 hcons Qtot hQ' hcoll' 4 hread4 j 3 hj (by omega)) h33) h34,
          before_trans v.1 (before_trans v.1
            (abs_before_abs p x msg ex H π v.1 hcons Qtot hQ' hcoll' 4 hread4 j 3 hj (by omega)) h33) h34⟩
      · obtain rfl : j = 3 := by omega
        exact ⟨h34, before_trans v.1 h33 h34⟩
  -- the decoded sampler
  have ha0 : a = absC p x msg ex H π i := by
    rw [firstCellQ p x msg H π i hi4] at ha
    exact (Option.some.inj ha).symm
  subst ha0
  set T := tableBefore emptyTable v.1 (absC p x msg ex H π i) with hT
  have hT' : ∀ b w, T b = some w → w = H b ∧ Read v.1 b := by
    intro b w hbw
    rw [hT, tableBefore_eq H v.1 emptyTable _ b hcons] at hbw
    split at hbw
    · rename_i hBb
      exact ⟨(Option.some.inj hbw).symm, hBb.1⟩
    · cases hbw
  have hTsome : ∀ b, Before v.1 b (absC p x msg ex H π i) → T b ≠ none := by
    intro b hBb
    rw [hT, tableBefore_eq H v.1 emptyTable _ b hcons, if_pos hBb]
    exact Option.some_ne_none _
  have hTnone : ∀ b, Before v.1 (absC p x msg ex H π i) b → T b = none := by
    intro b hBb
    rw [hT, tableBefore_eq H v.1 emptyTable _ b hcons, if_neg (fun h => lt_asymm h.2 hBb.2)]
    rfl
  have hwalk := walk_eq p x msg ex H π v.1 hcons Qtot hQ' hcoll' i
    (fun j hj => ⟨(hread4 j (by omega)).1, (hread4 j (by omega)).2.2⟩) i p.rounds le_rfl (by omega) T hT'
    (fun j hj => ⟨hTsome _ (hB j hj).1, hTsome _ (hB j hj).2⟩)
  have hlen : (recs p x msg ex H π i).length < 5 := by rw [recs_length]; omega
  set recsI := recs p x msg ex H π i with hrecsI
  set miss := missingQ p T recsI with hmiss
  set s0 := sv' p x msg ex H π i with hs0
  set a0 := absC p x msg ex H π i with ha0def
  set g : List State → List State → Prefix (Stmt E Sfield) (Msg E) DC × Msg E × DC :=
    fun xs as => (completePrefix p x T recsI (accFrom miss (as.take miss.length)), msg π i,
      outFor p i (as.drop miss.length) xs) with hg
  refine ⟨.ask a0 fun s' => chainBS p (nsteps i) s' [s'], miss.map fun c => (c, none), g, ?_, ?_⟩
  · simp only [decQ, ha0def, parseAbsorb_absC, p.decEnc, hwalk, if_pos hlen, recs_length, hg, hmiss,
      hrecsI]
    rw [if_pos (by omega)]
  -- membership in the missing list
  have hmissMem : ∀ c ∈ miss, ∃ j < i, c = squeezeA p (sv' p x msg ex H π j) ∧ T c = none := by
    intro c hc
    rw [hmiss, missingQ, List.mem_dedup, List.mem_filter, List.mem_map] at hc
    obtain ⟨⟨r, hr, rfl⟩, hnone⟩ := hc
    rw [hrecsI, recs_eq, List.mem_map] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    exact ⟨j, List.mem_range.mp hj, rfl, Option.isNone_iff_eq_none.mp hnone⟩
  -- chain facts
  have hchainRead : ∀ k < nsteps i, Read v.1 (squeezeA p (st p H s0 k)) ∧
      Read v.1 (advanceA p (st p H s0 k)) := by
    intro k hk
    rcases Nat.lt_or_ge i 4 with h | h
    · have hk0 : k = 0 := by simp only [nsteps, if_pos h] at hk; omega
      subst hk0
      exact ⟨(hread4 i h).2.1, (hread4 i h).2.2⟩
    · obtain rfl : i = 4 := by omega
      exact hchain4 k (by simpa [nsteps] using hk)
  have hstep : ∀ k, k + 1 < nsteps i →
      Before v.1 (advanceA p (st p H s0 k)) (squeezeA p (st p H s0 (k + 1))) ∧
      Before v.1 (advanceA p (st p H s0 k)) (advanceA p (st p H s0 (k + 1))) := by
    intro k hk
    exact ⟨noColl_prefix_after p Qtot H v.1 hcons hQ' hcoll' _ _ (hchainRead k (by omega)).2
        (hchainRead (k + 1) hk).1 (toBytes_squeezeA p _),
      noColl_prefix_after p Qtot H v.1 hcons hQ' hcoll' _ _ (hchainRead k (by omega)).2
        (hchainRead (k + 1) hk).2 (toBytes_advanceA p _)⟩
  have hn1 : 0 < nsteps i := by unfold nsteps; split <;> omega
  have hA : ∀ k < nsteps i, Before v.1 a0 (squeezeA p (st p H s0 k)) ∧
      Before v.1 a0 (advanceA p (st p H s0 k)) := by
    intro k
    induction k with
    | zero =>
        intro _
        exact ⟨noColl_prefix_after p Qtot H v.1 hcons hQ' hcoll' _ _ hreadA (hchainRead 0 hn1).1
            (toBytes_squeezeA p _),
          noColl_prefix_after p Qtot H v.1 hcons hQ' hcoll' _ _ hreadA (hchainRead 0 hn1).2
            (toBytes_advanceA p _)⟩
      | succ k ih =>
        intro hk
        have h1 := (ih (by omega)).2
        have h2 := hstep k hk
        exact ⟨before_trans v.1 h1 h2.1, before_trans v.1 h1 h2.2⟩
  have hAD : ∀ j k, j < k → k < nsteps i →
      Before v.1 (advanceA p (st p H s0 j)) (squeezeA p (st p H s0 k)) ∧
      Before v.1 (advanceA p (st p H s0 j)) (advanceA p (st p H s0 k)) := by
    intro j k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
        intro hjk hk
        rcases Nat.lt_or_ge j k with h | h
        · have h1 := (ih h (by omega)).2
          have h2 := hstep k hk
          exact ⟨before_trans v.1 h1 h2.1, before_trans v.1 h1 h2.2⟩
        · obtain rfl : j = k := by omega
          exact hstep j hk
  have hst : ∀ j k, j < k → k < nsteps i → st p H s0 j ≠ st p H s0 k := by
    intro j k hjk hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hrk := (hchainRead k' (by omega)).2
    show st p H s0 j ≠ H (advanceA p (st p H s0 k'))
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      show H a0 ≠ H (advanceA p (st p H s0 k'))
      exact noColl_injective p Qtot H v.1 hcons hQ' hcoll' _ _ hreadA hrk
        (fun e => advanceA_ne_absorbA p _ (sv p x msg ex H π i) (p.lbl i) (p.enc (msg π i)) (p.encLen _) e.symm)
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      show H (advanceA p (st p H s0 j')) ≠ H (advanceA p (st p H s0 k'))
      exact noColl_injective p Qtot H v.1 hcons hQ' hcoll' _ _ (hchainRead j' (by omega)).2 hrk
        (before_ne v.1 (hAD j' k' (by omega) (by omega)).2)
  have hneq : ∀ j < i, ∀ k < nsteps i, sv' p x msg ex H π j ≠ st p H s0 k := by
    intro j hj k hk
    have hrj : Read v.1 (absC p x msg ex H π j) := (hread4 j (by omega)).1
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      exact noColl_injective p Qtot H v.1 hcons hQ' hcoll' _ _ hrj hreadA (before_ne v.1 (hB j hj).2)
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact noColl_injective p Qtot H v.1 hcons hQ' hcoll' _ _ hrj (hchainRead k' (by omega)).2
        (fun e => advanceA_ne_absorbA p _ _ _ _ _ e.symm)
  have hchainMem : ∀ e ∈ evs H (chainBS p (nsteps i) s0 [s0]), ∃ k < nsteps i,
      e.2 = squeezeA p (st p H s0 k) ∨ e.2 = advanceA p (st p H s0 k) := by
    intro e he
    obtain ⟨k, hk, he'⟩ := evs_chainBS_mem p H _ s0 [s0] e he
    refine ⟨k, hk, ?_⟩
    rcases he' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- the follow conditions
  have hconsT : ∀ q ∈ traceFrom v.1 a0, q.2 = H q.1 := by
    obtain ⟨rest, hrest, hrc, _⟩ := traceFrom_eq H v.1 a0 hcons hreadA
    intro q hq
    rw [hrest] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact hrc q hq
  have hevs : evs H (BS.ask a0 fun s' => chainBS p (nsteps i) s' [s']) =
      (true, a0) :: evs H (chainBS p (nsteps i) s0 [s0]) := rfl
  have hnd : (waiting (miss.map fun c => ((c, none) : Addr L × Option State)) ++
      (evs H (BS.ask a0 fun s' => chainBS p (nsteps i) s' [s'])).map Prod.snd).Nodup := by
    rw [waiting_none, hevs, List.map_cons, List.nodup_append]
    refine ⟨List.nodup_dedup _, List.nodup_cons.mpr ⟨?_, chain_nodup p H _ s0 [s0] hst⟩, ?_⟩
    · intro hm
      obtain ⟨e, he, hea⟩ := List.mem_map.mp hm
      obtain ⟨k, _, hc⟩ := hchainMem e he
      rw [hea] at hc
      rcases hc with hc | hc
      · exact squeezeA_ne_absorbA p _ (sv p x msg ex H π i) (p.lbl i) (p.enc (msg π i)) (p.encLen _) hc.symm
      · exact advanceA_ne_absorbA p _ (sv p x msg ex H π i) (p.lbl i) (p.enc (msg π i)) (p.encLen _) hc.symm
    · intro c hc d hd hcd
      obtain ⟨j, hj, rfl, _⟩ := hmissMem c hc
      rcases List.mem_cons.mp hd with rfl | hd
      · exact squeezeA_ne_absorbA p _ (sv p x msg ex H π i) (p.lbl i) (p.enc (msg π i)) (p.encLen _) hcd
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
        obtain ⟨k, hk, hc'⟩ := hchainMem e he
        rcases hc' with hc' | hc'
        · rw [hc'] at hcd
          exact hneq j hj k hk (squeezeA_injective p hcd)
        · rw [hc'] at hcd
          exact squeezeA_ne_advanceA' p _ _ hcd
  have hafter : ∀ c, Read v.1 c → Before v.1 a0 c → T c = none ∧ Read (traceFrom v.1 a0) c :=
    fun c hc hBc => ⟨hTnone c hBc, read_traceFrom a0 c v.1 hreadA hc (Or.inr hBc)⟩
  have hfresh : ∀ c ∈ waiting (miss.map fun c => ((c, none) : Addr L × Option State)) ++
      (evs H (BS.ask a0 fun s' => chainBS p (nsteps i) s' [s'])).map Prod.snd,
      T c = none ∧ Read (traceFrom v.1 a0) c := by
    intro c hc
    rw [waiting_none, hevs, List.map_cons] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨j, hj, rfl, hTc⟩ := hmissMem c hc
      have hrc : Read v.1 (squeezeA p (sv' p x msg ex H π j)) := (hread4 j (by omega)).2.1
      have hne : a0 ≠ squeezeA p (sv' p x msg ex H π j) := fun e => squeezeA_ne_absorbA p _ (sv p x msg ex H π i) (p.lbl i) (p.enc (msg π i)) (p.encLen _) e.symm
      rcases before_total v.1 _ _ hreadA hrc hne with h | h
      · exact hafter _ hrc h
      · exact absurd hTc (hTsome _ h)
    · rcases List.mem_cons.mp hc with hca | hc
      · rw [hca]
        exact ⟨tableBefore_self H v.1 _ hcons, read_traceFrom a0 a0 v.1 hreadA hreadA (Or.inl rfl)⟩
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
        obtain ⟨k, hk, hc'⟩ := hchainMem e he
        rcases hc' with hc' | hc'
        · rw [hc']; exact hafter _ (hchainRead k hk).1 (hA k hk).1
        · rw [hc']; exact hafter _ (hchainRead k hk).2 (hA k hk).2
  have hord : OrderOK (traceFrom v.1 a0) (evs H (BS.ask a0 fun s' => chainBS p (nsteps i) s' [s'])) := by
    rw [hevs]
    apply order_traceFrom v.1 a0 hreadA
    · refine ⟨fun _ e he => ?_, order_chain p H v.1 _ s0 [s0] hAD⟩
      obtain ⟨k, hk, hc'⟩ := hchainMem e he
      rcases hc' with hc' | hc'
      · rw [hc']; exact (hA k hk).1
      · rw [hc']; exact (hA k hk).2
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact Or.inl rfl
      · obtain ⟨k, hk, hc'⟩ := hchainMem e he
        rcases hc' with hc' | hc'
        · rw [hc']; exact Or.inr (hA k hk).1
        · rw [hc']; exact Or.inr (hA k hk).2
  rw [bfollow_ok H g _ _ _ T hconsT hnd hfresh hord]
  -- the output
  have hrun : runOut H (BS.ask a0 fun s' => chainBS p (nsteps i) s' [s']) =
      ([s0] ++ (List.range (nsteps i)).map (fun k => st p H s0 (k + 1)),
        (List.range (nsteps i)).map (fun k => squeezeA p (st p H s0 k))) :=
    runOut_chainBS p H _ s0 [s0]
  have hfill : fill H (miss.map fun c => ((c, none) : Addr L × Option State)) = miss.map H := by
    simp [fill]
  rw [hrun, hfill, hg]
  simp only [List.map_map]
  rw [List.take_left' (by simp), List.drop_left' (by simp)]
  congr 1
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · show completePrefix p x T recsI (accFrom miss (miss.map H)) = (prQ).transcript H x π i
    rw [transcriptQ p x msg H π i hi4]
    have hstmt := transcript_statement p x msg ex H π i
    have hrounds : completeRounds p T (accFrom miss (miss.map H)) 0 recsI =
        ((prV).transcript H x π i).rounds := by
      apply completeRounds_recs
      intro j hj
      cases hTj : T (sqC p x msg ex H π j) with
      | some w => simp only [Option.getD_some]; exact (hT' _ _ hTj).1
      | none =>
          simp only [Option.getD_none]
          apply accFrom_map
          rw [hmiss, missingQ, List.mem_dedup, List.mem_filter, List.mem_map]
          refine ⟨⟨(sv p x msg ex H π j, sv' p x msg ex H π j, msg π j, H (adC p x msg ex H π j)), ?_, rfl⟩,
            by rw [Option.isNone_iff_eq_none]; exact hTj⟩
          rw [hrecsI, recs_eq, List.mem_map]
          exact ⟨j, List.mem_range.mpr hj, rfl⟩
    cases hP : (prV).transcript H x π i with
    | mk st' rs =>
        simp only [completePrefix]
        rw [hP] at hstmt hrounds
        simp only at hstmt hrounds
        rw [hstmt, hrounds]
  · show outFor p i _ _ = (prQ).chal H x π i
    rcases Nat.lt_or_ge i 4 with h | h
    · rw [chalQ_lt p x msg H π i h, chal_eq]
      simp only [outFor, if_pos h, nsteps, List.range_one, List.map_cons, List.map_nil,
        List.headD_cons, List.singleton_append, List.getD_cons_succ, List.getD_cons_zero]
      rfl
    · obtain rfl : i = 4 := by omega
      rw [chalQ_4]
      simp only [outFor, show ¬ (4 < 4) from by omega, if_false, nsteps, List.singleton_append,
        List.headD_cons, List.tail_cons]
      rfl


#print axioms decodesQ
end
end R0C.V3.DQ
