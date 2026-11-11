import R1OpeningQueryTrace
import AspisRec40FinalContext
import AspisRec40FollowPrefix

/-! The follow for rows 33 to 39 (`FollowStatement.FollowClaim`), proved for
every n with 33 ≤ n < 40, with R1's premises of
`UnifiedRhoInjection.decodes_and_follows` and nothing else.

Copy of R1's `JointNextTrace.follows_after_prefix_query` (row 32) with the
anchor moved to row n's frame `cn`:
* the pending cells are R1's joint missing cells at `T_n` (prefix records from
  `OpeningAnchorCells.cells_before_anchor` at anchor `cn`, the query states from
  the seek at `T_n`, as in `FinalContext.joint_at`) and the squeeze cells of rows
  32 .. n-1 absent from `T_n`; each is absent from `T_n`, read in the trace, and
  differs from `cn` and its two own cells (`PrefixPendingFacts.pending_facts`,
  `TableStateSeparation.known_ne_endpoint` with the frames of rows 32 .. n-1 in
  `T_n` by `FinalBefore.run_cells`);
* R1's generic `QueryOwnFollow.follow` then gives the output at the oracle's
  answers, and `FollowPrefix.prefix_part` identifies it with row n's actual
  prefix; the message and challenge are row n's (`FollowLists`). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FollowProof
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1 AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem squeezes_eq (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
    (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (n : Nat) (hlo : 33 ≤ n) (T : Table (Addr L) State)
    (hcells : ∀ j, j < n - 32 → T (UnifiedSteps.address p hD H pub c1 payload (32 + j)) =
      some (UnifiedRecords.absorbed p hD H pub c1 payload (32 + j))) :
    AspisRows40.Final.squeezes p T (AspisRec40.FollowStatement.actualCtx p hD H pub c1 payload n) =
      (List.range (n - 32)).map (fun j =>
        squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload (32 + j))) := by
  unfold AspisRows40.Final.squeezes
  rw [FollowLists.frames_eq p hD H pub c1 payload n hlo, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply]
  rw [hcells j (List.mem_range.mp hj)]
  rfl


section generic
variable (p : Params M Cv L) (H : Addr L → State) (tr : List (Addr L × State))

theorem squeeze_ne_frame (cn : Addr L) (hparse : (parseAbsorb cn).isSome) (s : State) :
    squeezeA p s ≠ cn := by
  intro heq
  have h := QueryDecoder.parseAbsorb_squeeze_none p s
  rw [heq] at h
  rw [h] at hparse
  simp only [Option.isSome_none, Bool.false_eq_true] at hparse

/-- Pending facts for a squeeze cell of a known state. -/
theorem squeeze_facts (T : Table (Addr L) State) (cn : Addr L)
    (hparse : (parseAbsorb cn).isSome) (s : State) (hread : Read tr (squeezeA p s))
    (hne : s ≠ H cn) (hnone : T (squeezeA p s) = none) :
    (T (squeezeA p s) = none ∧ Read tr (squeezeA p s)) ∧ squeezeA p s ≠ cn ∧
      squeezeA p s ≠ squeezeA p (H cn) ∧ squeezeA p s ≠ advanceA p (H cn) :=
  ⟨⟨hnone, hread⟩, squeeze_ne_frame p cn hparse s,
    fun heq => hne (squeezeA_injective p heq), squeezeA_ne_advanceA' p s (H cn)⟩

/-- The squeeze cells of rows 32 .. n-1 left pending. -/
theorem new_facts (T : Table (Addr L) State) (cn : Addr L)
    (hparse : (parseAbsorb cn).isSome) (ctx : AspisRows40.Context.Context M L)
    (m : Nat) (f : Nat → State)
    (hsq : AspisRows40.Final.squeezes p T ctx = (List.range m).map (fun j => squeezeA p (f j)))
    (hf : ∀ j < m, Read tr (squeezeA p (f j)) ∧ f j ≠ H cn) :
    ∀ b ∈ AspisRows40.Final.newMissing p T ctx, (T b = none ∧ Read tr b) ∧
      b ≠ cn ∧ b ≠ squeezeA p (H cn) ∧ b ≠ advanceA p (H cn) := by
  intro b hb
  unfold AspisRows40.Final.newMissing at hb
  rw [List.mem_dedup, List.mem_filter, hsq] at hb
  obtain ⟨hbs, hcond⟩ := hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hbs
  have hnone : T (squeezeA p (f j)) = none := by
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hcond
    exact hcond.1
  have hj' := List.mem_range.mp hj
  exact squeeze_facts p H tr T cn hparse (f j) (hf j hj').1 (hf j hj').2 hnone

theorem new_disjoint (T : Table (Addr L) State) (ctx : AspisRows40.Context.Context M L) :
    ∀ b ∈ AspisRows40.Final.jointMissing p T ctx, b ∉ AspisRows40.Final.newMissing p T ctx := by
  intro b hb hb2
  unfold AspisRows40.Final.newMissing at hb2
  rw [List.mem_dedup, List.mem_filter] at hb2
  have h := hb2.2
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  exact h.2 hb

/-- R1's joint pending cells (prefix records and query states). -/
theorem joint_facts (T : Table (Addr L) State) (cn : Addr L)
    (hparse : (parseAbsorb cn).isSome) (rs : List (Rec M)) (e : State)
    (hpending : ∀ b ∈ PrefixAnswers.missing p T rs, T b = none ∧ Read tr b ∧
      b ≠ cn ∧ b ≠ squeezeA p (H cn) ∧ b ≠ advanceA p (H cn))
    (a : Addr L) (qs : Nat → State) (K : Nat)
    (hseek : DuplexSeek.seek p T 9 e = some (a, QueryStateList.states qs K))
    (hq : ∀ j < K, Read tr (squeezeA p (qs j)) ∧ qs j ≠ H cn) :
    ∀ b ∈ JointPrefixAnswers.missing p T rs e, (T b = none ∧ Read tr b) ∧
      b ≠ cn ∧ b ≠ squeezeA p (H cn) ∧ b ≠ advanceA p (H cn) := by
  intro b hb
  rcases JointPrefixAnswers.missing_cases p T rs e b hb with hp | hqm
  · have h := hpending b hp
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · obtain ⟨j, hj, rfl, hn⟩ := QueryDecoder.missing_mem_states p T e a qs K hseek b hqm
    exact squeeze_facts p H tr T cn hparse (qs j) (hq j hj).1 (hq j hj).2 hn

/-- R1's query recovery at a later consistent table. -/
theorem recover_at (T T' : Table (Addr L) State)
    (hT : ∀ b v, T b = some v → v = H b) (hT' : ∀ b v, T' b = some v → v = H b)
    (e : State) (a : Addr L) (qs : Nat → State) (K : Nat)
    (r : AspisV8R19.Q22SamplerProgram.Result)
    (hseek : DuplexSeek.seek p T 9 e = some (a, QueryStateList.states qs K))
    (hcomplete : QueryCompletion.complete p T' H (QueryStateList.states qs K) = r) :
    QueryDecoder.recover p T H e = some (a, r) := by
  unfold QueryDecoder.recover
  rw [hseek]
  show some (a, QueryCompletion.complete p T H (QueryStateList.states qs K)) = some (a, r)
  have h1 := QueryCompletion.complete_states p T H H qs K (fun j _ =>
    QueryCompletion.getter_correct T H H _ hT (fun _ => rfl))
  have h2 := QueryCompletion.complete_states p T' H H qs K (fun j _ =>
    QueryCompletion.getter_correct T' H H _ hT' (fun _ => rfl))
  rw [h1, ← h2, hcomplete]

/-- The template body (`JointNextTrace.follows_after_prefix_query`), generic. -/
theorem own_follow (hcons : ∀ q ∈ tr, q.2 = H q.1) (cn : Addr L) (hcnread : Read tr cn)
    (miss : List (Addr L)) {C : Type} (g : State → List State → C)
    (hndm : miss.Nodup)
    (hsep : ∀ b ∈ miss, (tableBefore emptyTable tr cn b = none ∧ Read tr b) ∧
      b ≠ cn ∧ b ≠ squeezeA p (H cn) ∧ b ≠ advanceA p (H cn))
    (hnewsq : Read tr (squeezeA p (H cn))) (hnewadv : Read tr (advanceA p (H cn)))
    (hbsq : Before tr cn (squeezeA p (H cn))) (hbadv : Before tr cn (advanceA p (H cn))) :
    bfollow g (traceFrom tr cn) (QueryNextLaw.own p cn) (miss.map fun b => (b, none))
        (tableBefore emptyTable tr cn) =
      some (g (H (advanceA p (H cn))) (miss.map H ++ [H (squeezeA p (H cn))])) := by
  have hnd : (miss ++ [cn, squeezeA p (H cn), advanceA p (H cn)]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hndm, ?_, ?_⟩
    · simp [before_ne tr hbsq, before_ne tr hbadv, squeezeA_ne_advanceA p (H cn)]
    · intro b hb d hd hbd
      have hbown : b ∈ [cn, squeezeA p (H cn), advanceA p (H cn)] := by
        rw [hbd]; exact hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbown
      rcases hbown with heq | heq | heq
      · exact (hsep b hb).2.1 heq
      · exact (hsep b hb).2.2.1 heq
      · exact (hsep b hb).2.2.2 heq
  have hfresh : ∀ b ∈ miss ++ [cn, squeezeA p (H cn), advanceA p (H cn)],
      tableBefore emptyTable tr cn b = none ∧ Read (traceFrom tr cn) b := by
    intro b hb
    have hpair : tableBefore emptyTable tr cn b = none ∧ Read tr b := by
      rcases List.mem_append.mp hb with hb | hb
      · exact (hsep b hb).1
      · rcases List.mem_cons.mp hb with heq | hb
        · rw [heq]
          exact ⟨tableBefore_self H tr cn hcons, hcnread⟩
        · rcases List.mem_cons.mp hb with heq | hb
          · rw [heq]
            exact ⟨TraceSuffix.after_absent H tr cn _ hcons hbsq, hnewsq⟩
          · have hb' := List.mem_singleton.mp hb
            rw [hb']
            exact ⟨TraceSuffix.after_absent H tr cn _ hcons hbadv, hnewadv⟩
    exact ⟨hpair.1, TraceSuffix.absent_read H tr cn b hcons hcnread hpair.2 hpair.1⟩
  exact QueryOwnFollow.follow p H (traceFrom tr cn) (tableBefore emptyTable tr cn) cn miss g
    (TraceSuffix.traceFrom_consistent H tr cn hcons hcnread) hnd hfresh
    (DQ.before_traceFrom cn cn _ tr hcnread (Or.inl rfl) hbsq)
    (DQ.before_traceFrom cn cn _ tr hcnread (Or.inl rfl) hbadv)

end generic

theorem follow (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool) :
    AspisRec40.FollowStatement.FollowClaim p hD extract decision := by
  intro H pub c1 payload prior hprior hpub hl he Qtot hQ hold htail n hlo hhi tr cn Tn ctx
  let a := UnifiedQueryRun.queryAddress p hD H pub c1 payload
  let c := UnifiedQueryRun.rhoAddress p hD H pub c1 payload
  let ss := UnifiedPhases.semanticState p hD H pub c1 payload
  let sb := UnifiedRecords.absorbed p hD H pub c1 payload
  let os := UnifiedPhases.openingState p hD H pub c1 payload
  let ob := fun j => UnifiedRecords.absorbed p hD H pub c1 payload (27 + j)
  let om := fun j => payload (27 + j)
  let qs := QuerySampler.state p H (H a)
  let rs := UnifiedRecords.records p hD H pub c1 payload 31
  let qr := UnifiedQueryRun.queryResult p hD H pub c1 payload
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    AspisRec40.FinalRun.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hi : Read tr (PublicInitFrame.addr pub.pubBytes pub.initFits c1) :=
    AspisRec40.FinalRun.initial_read p hD extract decision H pub c1 payload prior
  have hreads (i : Nat) (hi : i < 40) (hi31 : i ≠ 31) :=
    AspisRec40.FinalRun.ordinary_reads p hD extract decision H pub c1 payload prior hl he i
      hi hi31
  have hsabs (j : Nat) (hj : j < 27) :
      sb j = H (absorbA p (ss j) (p.lbl j) (p.enc (payload j)) (p.encLen _)) := by
    change _ = H (absorbA p (UnifiedPhases.semanticState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.semantic_before p hD H pub c1 payload j hj]
    rfl
  have hsar (j : Nat) (hj : j < 27) :
      Read tr (absorbA p (ss j) (p.lbl j) (p.enc (payload j)) (p.encLen _)) := by
    change Read tr (absorbA p (UnifiedPhases.semanticState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.semantic_before p hD H pub c1 payload j hj]
    exact (hreads j (by omega) (by omega)).1
  have h62 : 62 ≤ L := by have := pub.initFits; omega
  have hr : Read tr (OpeningReseedFrame.addr pub.tag h62 (ss 27)) := by
    change Read tr (OpeningReseedFrame.addr pub.tag h62
      (UnifiedPhases.semanticState p hD H pub c1 payload 27))
    rw [UnifiedPhases.semantic_end]
    exact AspisRec40.FinalRun.reseed_read p hD extract decision H pub c1 payload prior
  have horoot : os 0 = H (OpeningReseedFrame.addr pub.tag h62 (ss 27)) := by
    change UnifiedPhases.openingState p hD H pub c1 payload 0 =
      H (OpeningReseedFrame.addr pub.tag h62
        (UnifiedPhases.semanticState p hD H pub c1 payload 27))
    rw [UnifiedPhases.semantic_end]
    exact UnifiedPhases.opening_root p hD H pub c1 payload
  have hoabs (j : Nat) (hj : j < 4) :
      ob j = H (absorbA p (os j) (p.lbl (27 + j)) (p.enc (om j)) (p.encLen _)) := by
    change _ = H (absorbA p (UnifiedPhases.openingState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.opening_previous]
    rfl
  have hoar (j : Nat) (hj : j < 4) :
      Read tr (absorbA p (os j) (p.lbl (27 + j)) (p.enc (om j)) (p.encLen _)) := by
    change Read tr (absorbA p (UnifiedPhases.openingState p hD H pub c1 payload j) _ _ _)
    rw [UnifiedPhases.opening_previous]
    exact (hreads (27 + j) (by omega) (by omega)).1
  have hqr := AspisRec40.FinalRun.query_reads p hD extract decision H pub c1 payload prior
  have ha : Read tr a := hqr.1
  have hca0 : c = UnifiedSteps.address p hD H pub c1 payload 32 :=
    UnifiedSteps.payload_address p hD H pub c1 payload 32 (by decide)
  have hc : Read tr c := by rw [hca0]; exact (hreads 32 (by decide) (by decide)).1
  have hqa : a = absorbA p (os 4) (p.lbl 31) (p.enc (payload 31)) (p.encLen _) := by
    change UnifiedSampler.absorb p 31 (UnifiedRun.transcript p hD H pub c1 payload 31)
      (payload 31) = absorbA p (UnifiedPhases.openingState p hD H pub c1 payload 4) _ _ _
    rw [UnifiedSteps.payload_address p hD H pub c1 payload 31 (by decide),
      UnifiedPhases.opening_previous]
    rfl
  have hca : c = absorbA p (QueryFirstRead.result p H qs).2 (p.lbl 32)
      (p.enc (payload 32)) (p.encLen _) :=
    UnifiedQueryRun.rho_address p hD H pub c1 payload
  have hparsea' : parseAbsorb a = some (os 4, p.lbl 31, p.enc (payload 31)) := by
    rw [hqa, parseAbsorb_absorbA]
  have hparsea : (parseAbsorb a).isSome := by rw [hparsea']; rfl
  have haprefix : a.toBytes.take 32 = bytes (os 4) := by
    rw [hqa]; exact toBytes_absorbA p _ _ _ _
  have hcprefix : c.toBytes.take 32 = bytes (QueryFirstRead.result p H qs).2 := by
    rw [hca]; exact toBytes_absorbA p _ _ _ _
  -- row n's frame: read, parsed, its answer is row n's absorbed state
  have hfr := AspisRec40.FinalRun.final_reads p hD extract decision H pub c1 payload prior
    hl he n (by omega) hhi
  have hcnread : Read tr cn := hfr.1
  have hcnabs : H cn = UnifiedRecords.absorbed p hD H pub c1 payload n := rfl
  have hparsecn : (parseAbsorb cn).isSome := by
    change (parseAbsorb (UnifiedSteps.address p hD H pub c1 payload n)).isSome
    rw [AspisRec40.FinalContext.parse_address]; rfl
  have hnewsq : Read tr (squeezeA p (H cn)) := by rw [hcnabs]; exact hfr.2.1
  have hnewadv : Read tr (advanceA p (H cn)) := by rw [hcnabs]; exact hfr.2.2
  -- row 32's frame is read before row n's frame (fact (a))
  have hcn : Before tr c cn := by
    rw [hca0]
    exact (AspisRec40.FinalBefore.run_cells p hD extract decision H pub c1 payload prior hprior
      hl he Qtot hQ hold n hhi 32 (le_refl _) (by omega)).1
  -- the frames of rows 32 .. n-1 in T_n
  have hcellsn : ∀ j, j < n - 32 → Tn (UnifiedSteps.address p hD H pub c1 payload (32 + j)) =
      some (UnifiedRecords.absorbed p hD H pub c1 payload (32 + j)) := by
    intro j hj
    obtain ⟨_, _, habs, _⟩ := AspisRec40.FinalBefore.run_cells p hD extract decision H pub c1
      payload prior hprior hl he Qtot hQ hold n hhi (32 + j) (by omega) (by omega)
    exact habs
  -- the query chain at T_n
  have hqstep : ∀ j < 8, qs (j + 1) = H (advanceA p (qs j)) :=
    fun j _ => QuerySamplerBridge.state_step p H (H a) j
  have hqadv : ∀ j < 8, Read tr (advanceA p (qs j)) := fun j hj => (hqr.2 j hj).2
  obtain ⟨k, hk, hselected, hseek32, hcomplete⟩ := QueryFirstRead.recover_query_before_endpoint
    p H tr Qtot hcons hQ hold qs hqstep hqadv a c ha hc hparsea rfl hcprefix
  have hqcells := DuplexPrefixTable.table_cells p H tr Qtot hcons hQ hold qs (k + 1)
    (fun t _ => hqstep t (by omega)) (fun t _ => hqadv t (by omega))
    c a hc ha (by rw [← hselected]; exact hcprefix) rfl
  have hac : Before tr a c :=
    TableBeforeOrder.before_of_cell H tr hcons c a (qs 0) hqcells.1
  have hT : ∀ b v, Tn b = some v → v = H b ∧ Read tr b :=
    DuplexPrefixTable.table_consistent H tr hcons cn
  have hT32 : ∀ b v, tableBefore emptyTable tr c b = some v → v = H b ∧ Read tr b :=
    DuplexPrefixTable.table_consistent H tr hcons c
  have hseek := DuplexSeek.seek_of_noColl p Tn H tr Qtot (k + 1) 9 hcons hQ hold hT qs a
    hparsea rfl (FinalContext.table_mono H tr hcons c cn hcn a (qs 0) hqcells.1)
    (fun t ht => hqstep t (by omega))
    (fun t ht => FinalContext.table_mono H tr hcons c cn hcn _ _ (hqcells.2 t ht)) (by omega)
  rw [← hselected] at hseek
  -- R1's query recovery at T_n
  have hrec : QueryDecoder.recover p Tn H qr.2 = some (a, qr) :=
    recover_at p H Tn (tableBefore emptyTable tr c) (fun b v hb => (hT b v hb).1)
      (fun b v hb => (hT32 b v hb).1) _ a qs (k + 1) qr hseek (hcomplete H (fun _ _ _ => rfl))
  -- query states differ from row n's answer
  have hqne : ∀ j < k + 1, qs j ≠ H cn := by
    intro j hj
    rcases j with _ | t
    · exact TableStateSeparation.known_ne_endpoint p H tr Qtot hcons hQ hold cn hcnread a
        (qs 0) (FinalContext.table_mono H tr hcons c cn hcn a (qs 0) hqcells.1)
    · exact TableStateSeparation.known_ne_endpoint p H tr Qtot hcons hQ hold cn hcnread _
        (qs (t + 1)) (FinalContext.table_mono H tr hcons c cn hcn _ _ (hqcells.2 t (by omega)))
  -- prefix records at T_n (anchor cn)
  have hcells := OpeningAnchorCells.cells_before_anchor p pub.pubBytes hpub pub.initFits c1
    pub.tag h62 H tr Qtot hcons hQ hold htail 27 27 (by decide) (le_refl _)
    ss sb p.lbl (fun t => p.enc (payload t)) (fun j => p.encLen (payload j))
    (UnifiedPhases.semantic_root p hD H pub c1 payload) hi hsabs
    (UnifiedPhases.semantic_step p hD H pub c1 payload hl he) hsar
    (fun j hj => (hreads j (by omega) (by omega)).2.2) hr
    4 4 (le_refl _) os ob (fun t => p.lbl (26 + 1 + t)) (fun t => p.enc (om t))
    (fun j => p.encLen (om j)) horoot hoabs
    (UnifiedPhases.opening_step p hD H pub c1 payload hl he) hoar
    (fun j hj => (hreads (27 + j) (by omega) (by omega)).2.2)
    a cn ha haprefix (before_trans tr hac hcn)
  have hknown : ∀ r ∈ rs, ∃ b, Tn b = some r.2.1 := by
    change ∀ r ∈ UnifiedRecords.records p hD H pub c1 payload 31, _
    rw [← UnifiedPhaseRecords.ordinary_eq_records]
    exact PrefixRecordFacts.ordinary_known Tn ss sb payload 26 os ob om 4
      (fun t ht => ⟨_, (hcells.2.1 t ht).1⟩) (fun t ht => ⟨_, (hcells.2.2.2 t ht).1⟩)
  have hprefixreads : ∀ r ∈ rs, Read tr (squeezeA p r.2.1) := by
    change ∀ r ∈ UnifiedRecords.records p hD H pub c1 payload 31, _
    rw [← UnifiedPhaseRecords.ordinary_eq_records]
    exact PrefixRecordFacts.ordinary_reads p tr ss sb payload 26 os ob om 4
      (fun j hj => (hreads j (by omega) (by omega)).2.1)
      (fun j hj => (hreads (27 + j) (by omega) (by omega)).2.1)
  have hpending := PrefixPendingFacts.pending_facts p H tr Qtot hcons hQ hold cn hcnread
    hparsecn rs hknown hprefixreads
  -- facts on the pending cells
  have hjm := joint_facts p H tr Tn cn hparsecn rs qr.2 hpending a qs (k + 1) hseek
    (fun j hj => ⟨(hqr.2 j (by omega)).1, hqne j hj⟩)
  have hsq : AspisRows40.Final.squeezes p Tn ctx = (List.range (n - 32)).map (fun j =>
      squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload (32 + j))) :=
    squeezes_eq p hD H pub c1 payload n hlo Tn hcellsn
  have hnm := new_facts p H tr Tn cn hparsecn ctx (n - 32)
    (fun j => UnifiedRecords.absorbed p hD H pub c1 payload (32 + j)) hsq
    (fun j hj => ⟨(hreads (32 + j) (by omega) (by omega)).2.1,
      TableStateSeparation.known_ne_endpoint p H tr Qtot hcons hQ hold cn hcnread _ _
        (hcellsn j hj)⟩)
  have hsep : ∀ b ∈ AspisRows40.Final.missing p Tn ctx, (Tn b = none ∧ Read tr b) ∧
      b ≠ cn ∧ b ≠ squeezeA p (H cn) ∧ b ≠ advanceA p (H cn) := by
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact hjm b h
    · exact hnm b h
  have hndm : (AspisRows40.Final.missing p Tn ctx).Nodup := by
    unfold AspisRows40.Final.missing
    rw [List.nodup_append]
    refine ⟨JointPrefixAnswers.missing_nodup p Tn rs qr.2, List.nodup_dedup _, ?_⟩
    intro b hb d hd hbd
    rw [hbd] at hb
    exact new_disjoint p Tn ctx d hb hd
  have hbsq : Before tr cn (squeezeA p (H cn)) :=
    noColl_prefix_after p Qtot H tr hcons hQ hold cn (squeezeA p (H cn))
      hcnread hnewsq (toBytes_squeezeA p (H cn))
  have hbadv : Before tr cn (advanceA p (H cn)) :=
    noColl_prefix_after p Qtot H tr hcons hQ hold cn (advanceA p (H cn))
      hcnread hnewadv (toBytes_advanceA p (H cn))
  have hfollow := own_follow p H tr hcons cn hcnread (AspisRows40.Final.missing p Tn ctx)
    (AspisRows40.Final.output p pub Tn n ctx) hndm hsep hnewsq hnewadv hbsq hbadv
  refine Eq.trans hfollow ?_
  rw [AspisRows40.Final.output_append p pub Tn n ctx _ _ _ (List.length_map _)]
  have hpre : AspisRows40.Final.prefixOf p pub Tn ctx
      ((AspisRows40.Final.missing p Tn ctx).map H) =
      UnifiedRun.transcript p hD H pub c1 payload n :=
    FollowPrefix.prefix_part p hD H pub c1 payload hl he n hlo Tn
      (fun b v hb => (hT b v hb).1) hrec hcellsn
  have hmsg : (Message.payload ctx.message : Message M) = UnifiedRun.message c1 payload n :=
    (FollowLists.message_payload c1 payload n (by omega)).symm
  rw [hpre, hmsg, FollowLists.challenge_plain p hD H pub c1 payload n (by omega), hcnabs]
  rfl

#print axioms squeezes_eq
#print axioms squeeze_ne_frame
#print axioms squeeze_facts
#print axioms new_facts
#print axioms new_disjoint
#print axioms joint_facts
#print axioms recover_at
#print axioms own_follow
#print axioms follow

end AspisRec40.FollowProof
end
