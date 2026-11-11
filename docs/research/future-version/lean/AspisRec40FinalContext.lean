import R1UnifiedRecovery
import R1QueryFirstRead
import R1TableBeforeOrder
import R1JointContext
import AspisRec40FinalBefore
import AspisRec40FollowStatement
import AspisRows40Context

/-! Context recovery at the table before row n's frame (33 ≤ n < 40), on the
40-row address-level run (`AspisRec40.FinalRun.trace`), with R1's premise list
of `UnifiedRhoInjection.decodes_and_follows` (as in
`AspisRec40.FollowStatement.FollowClaim`).

`joint_at`: R1's row-32 parser `JointContext.parse … 27 4` at row 32's frame
returns R1's actual row-32 context also at the later table `T_n`. Copy of the
`hcontext` step of `UnifiedRhoInjection.decodes_and_follows`, with the table
taken before row n's frame instead of row 32's:
- the typed prefix walk from R1's anchor-parametric
  `OpeningPrefixAnchor.walk_before_anchor` (anchor := row n's frame, order from
  `TableBeforeOrder.before_of_cell` at row 32 and
  `AspisRec40.FinalBefore.run_cells`), then `OpeningPrefixCompletion.typed_of_walk`;
- the query seek from R1's `DuplexSeek.seek_of_noColl` at `T_n`, its cells taken
  from `DuplexPrefixTable.table_cells` at row 32's frame and carried to `T_n`
  (`table_mono`).

`context_at`: the Aspis parser `AspisRows40.Context.parse` at row n's frame and
`T_n` returns the actual context `FollowStatement.actualCtx n`: one seek of
fuel 2 for each of rows 32 .. n-1 (`seek_row`, from `seek_of_noColl` and
fact (a), `AspisRec40.FinalBefore.run_cells`), the indexed messages of rows
33 .. n-1 and n, and `joint_at`. Model level. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalContext
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1 AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

/-- A cell of the table before `c` is a cell of the table before any later `d`. -/
theorem table_mono (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (c d : Addr L) (hcd : Before tr c d)
    (b : Addr L) (v : State) (hb : tableBefore emptyTable tr c b = some v) :
    tableBefore emptyTable tr d b = some v := by
  have hbc : Before tr b c := TableBeforeOrder.before_of_cell H tr hcons c b v hb
  rw [tableBefore_eq H tr emptyTable c b hcons, if_pos hbc] at hb
  rw [tableBefore_eq H tr emptyTable d b hcons, if_pos (before_trans tr hbc hcd)]
  exact hb

theorem parse_address (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (i : Nat) :
    parseAbsorb (UnifiedSteps.address p hD H pub c1 payload i) =
      some (UnifiedRecords.previous p hD H pub c1 payload i, p.lbl i, p.enc (payload i)) := by
  unfold UnifiedSteps.address
  rw [parseAbsorb_absorbA]

/-- W1, first part: R1's row-32 context at the table before row n's frame. -/
theorem joint_at (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40) :
    JointContext.parse p pub.pubBytes pub.tag 27 4 (UnifiedSteps.address p hD H pub c1 payload 32)
        (tableBefore emptyTable
          (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) =
      some (AspisRec40.FollowStatement.jointCtx p hD H pub c1 payload) := by
  let tr := AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior
  let cn := UnifiedSteps.address p hD H pub c1 payload n
  let Tn := tableBefore emptyTable tr cn
  let a := UnifiedQueryRun.queryAddress p hD H pub c1 payload
  let c := UnifiedQueryRun.rhoAddress p hD H pub c1 payload
  let ss := UnifiedPhases.semanticState p hD H pub c1 payload
  let sb := UnifiedRecords.absorbed p hD H pub c1 payload
  let os := UnifiedPhases.openingState p hD H pub c1 payload
  let ob := fun j => UnifiedRecords.absorbed p hD H pub c1 payload (27 + j)
  let om := fun j => payload (27 + j)
  let qs := QuerySampler.state p H (H a)
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    AspisRec40.FinalRun.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hi : Read tr (PublicInitFrame.addr pub.pubBytes pub.initFits c1) :=
    AspisRec40.FinalRun.initial_read p hD extract decision H pub c1 payload prior
  have hreads (i : Nat) (hi : i < 33) (hi31 : i ≠ 31) :=
    AspisRec40.FinalRun.ordinary_reads p hD extract decision H pub c1 payload prior hl he i
      (by omega) hi31
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
  -- row 32's frame is read before row n's frame (fact (a))
  have hcn : Before tr c cn := by
    rw [hca0]
    exact (AspisRec40.FinalBefore.run_cells p hD extract decision H pub c1 payload prior hprior
      hl he Qtot hQ hold n hhi 32 (le_refl _) (by omega)).1
  -- the query chain: selected index, cells before row 32's frame, carried to T_n
  have hqstep : ∀ j < 8, qs (j + 1) = H (advanceA p (qs j)) :=
    fun j _ => QuerySamplerBridge.state_step p H (H a) j
  have hqadv : ∀ j < 8, Read tr (advanceA p (qs j)) := fun j hj => (hqr.2 j hj).2
  obtain ⟨k, hk, hselected, _, _⟩ := QueryFirstRead.recover_query_before_endpoint
    p H tr Qtot hcons hQ hold qs hqstep hqadv a c ha hc hparsea rfl hcprefix
  have hqcells := DuplexPrefixTable.table_cells p H tr Qtot hcons hQ hold qs (k + 1)
    (fun t _ => hqstep t (by omega)) (fun t _ => hqadv t (by omega))
    c a hc ha (by rw [← hselected]; exact hcprefix) rfl
  have hac : Before tr a c :=
    TableBeforeOrder.before_of_cell H tr hcons c a (qs 0) hqcells.1
  have hT : ∀ b v, Tn b = some v → v = H b ∧ Read tr b :=
    DuplexPrefixTable.table_consistent H tr hcons cn
  have hseek := DuplexSeek.seek_of_noColl p Tn H tr Qtot (k + 1) 9 hcons hQ hold hT qs a
    hparsea rfl (table_mono H tr hcons c cn hcn a (qs 0) hqcells.1)
    (fun t ht => hqstep t (by omega))
    (fun t ht => table_mono H tr hcons c cn hcn _ _ (hqcells.2 t ht)) (by omega)
  rw [← hselected] at hseek
  -- the typed prefix walk at anchor row n's frame
  have hwalk := OpeningPrefixAnchor.walk_before_anchor p pub.pubBytes hpub pub.initFits c1
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
  have htyped := OpeningPrefixCompletion.typed_of_walk p pub.pubBytes pub.tag Tn 27 4
    (os 4) c1 ss sb payload 26 os ob om 4 hwalk
  have htyped' : OpeningPrefixCompletion.typed p pub.pubBytes pub.tag Tn 27 4 (os 4) =
      some (c1, UnifiedRecords.records p hD H pub c1 payload 31) := by
    rw [← UnifiedPhaseRecords.ordinary_eq_records]
    exact htyped
  have hlen : (UnifiedRecords.records p hD H pub c1 payload 31).length = 31 :=
    UnifiedRecords.records_length p hD H pub c1 payload 31
  have hparsec : parseAbsorb (UnifiedSteps.address p hD H pub c1 payload 32) =
      some ((UnifiedQueryRun.queryResult p hD H pub c1 payload).2, p.lbl 32,
        p.enc (payload 32)) := by
    rw [← hca0, hca, parseAbsorb_absorbA]
    rfl
  exact JointContext.parse_of_checks p pub.pubBytes pub.tag 27 4 _ Tn
    (UnifiedQueryRun.queryResult p hD H pub c1 payload).2 _ _ a _ (os 4) _ _ c1
    (UnifiedRecords.records p hD H pub c1 payload 31) (payload 31) (payload 32)
    hparsec hseek hparsea' htyped'
    (by rw [hlen]; exact IndexedMessage.read_encoded p 31 (payload 31))
    (by rw [hlen]; exact IndexedMessage.read_encoded p 32 (payload 32))

/-- One plain row back (rows 32 .. n-1): from the state before row j+1 the
seek of fuel 2 at `T_n` finds row j's frame. -/
theorem seek_row (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hhi : n < 40) (j : Nat) (hlo : 32 ≤ j) (hj : j < n) :
    ∃ xs, DuplexSeek.seek p
        (tableBefore emptyTable
          (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) 2
        (UnifiedRecords.previous p hD H pub c1 payload (j + 1)) =
      some (UnifiedSteps.address p hD H pub c1 payload j, xs) := by
  let tr := AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    AspisRec40.FinalRun.trace_consistent p hD extract decision H pub c1 payload prior hprior
  obtain ⟨_, _, habs, hadv⟩ := AspisRec40.FinalBefore.run_cells p hD extract decision H pub c1
    payload prior hprior hl he Qtot hQ hold n hhi j hlo hj
  let s : Nat → State := fun i => match i with
    | 0 => UnifiedRecords.absorbed p hD H pub c1 payload j
    | _ + 1 => UnifiedRecords.previous p hD H pub c1 payload (j + 1)
  have hstep : ∀ i < 1, s (i + 1) = H (advanceA p (s i)) := by
    intro i hi
    have : i = 0 := by omega
    subst this
    exact AspisRec40.FinalRun.final_state_step p hD H pub c1 payload hl he j hlo
  have hseek := DuplexSeek.seek_of_noColl p
    (tableBefore emptyTable tr (UnifiedSteps.address p hD H pub c1 payload n)) H tr Qtot 1 2
    hcons hQ hold (DuplexPrefixTable.table_consistent H tr hcons _) s
    (UnifiedSteps.address p hD H pub c1 payload j)
    (by rw [parse_address]; rfl) rfl habs hstep
    (by
      intro i hi
      have : i = 0 := by omega
      subst this
      exact hadv) (le_refl _)
  exact ⟨_, hseek⟩

/-- The walk back from the state before row `33 + k` reaches row 32's frame,
passing the frames of rows 33 .. 32+k. -/
theorem back_run (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hhi : n < 40) :
    ∀ k, 33 + k ≤ n →
      AspisRows40.Context.back p
        (tableBefore emptyTable
          (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) k
        (UnifiedRecords.previous p hD H pub c1 payload (33 + k)) =
      some (UnifiedSteps.address p hD H pub c1 payload 32,
        (List.range k).map fun i => UnifiedSteps.address p hD H pub c1 payload (33 + i)) := by
  intro k
  induction k with
  | zero =>
      intro hk
      obtain ⟨xs, hs⟩ := seek_row p hD extract decision H pub c1 payload prior hprior hl he
        Qtot hQ hold n hhi 32 (le_refl _) (by omega)
      simp only [AspisRows40.Context.back]
      rw [show (33 + 0 : Nat) = 32 + 1 from rfl, hs]
      rfl
  | succ k ih =>
      intro hk
      obtain ⟨xs, hs⟩ := seek_row p hD extract decision H pub c1 payload prior hprior hl he
        Qtot hQ hold n hhi (33 + k) (by omega) (by omega)
      simp only [AspisRows40.Context.back]
      rw [show 33 + (k + 1) = 33 + k + 1 by omega, hs]
      simp only [Option.bind_some, parse_address]
      rw [ih (by omega)]
      simp only [Option.map_some, List.range_succ, List.map_append, List.map_cons,
        List.map_nil]

/-- The messages of rows `j .. j+m-1` are read back at their indexed labels. -/
theorem readTail_run (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M) :
    ∀ m j, AspisRows40.Context.readTail p j
        ((List.range m).map fun i => UnifiedSteps.address p hD H pub c1 payload (j + i)) =
      some ((List.range m).map fun i =>
        (UnifiedSteps.address p hD H pub c1 payload (j + i), payload (j + i))) := by
  intro m
  induction m with
  | zero => intro j; rfl
  | succ m ih =>
      intro j
      rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
      simp only [AspisRows40.Context.readTail, parse_address, Option.bind_some,
        Nat.add_zero, IndexedMessage.read_encoded]
      have h := ih (j + 1)
      have e1 : ((fun i => UnifiedSteps.address p hD H pub c1 payload (j + i)) ∘ Nat.succ) =
          fun i => UnifiedSteps.address p hD H pub c1 payload (j + 1 + i) := by
        funext i; simp only [Function.comp, Nat.succ_eq_add_one]; congr 1; omega
      have e2 : ((fun i => (UnifiedSteps.address p hD H pub c1 payload (j + i), payload (j + i)))
          ∘ Nat.succ) = fun i =>
            (UnifiedSteps.address p hD H pub c1 payload (j + 1 + i), payload (j + 1 + i)) := by
        funext i; simp only [Function.comp, Nat.succ_eq_add_one]
        rw [show j + (i + 1) = j + 1 + i by omega]
      rw [e1, h, e2]
      rfl

/-- W1, second part: the Aspis context parser at row n's frame and the table
before it returns the actual context of row n. -/
theorem context_at (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior))
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40) :
    AspisRows40.Context.parse p pub.pubBytes pub.tag n (UnifiedSteps.address p hD H pub c1 payload n)
        (tableBefore emptyTable
          (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior)
          (UnifiedSteps.address p hD H pub c1 payload n)) =
      some (AspisRec40.FollowStatement.actualCtx p hD H pub c1 payload n) := by
  have hj := joint_at p hD extract decision H pub c1 payload prior hprior hpub hl he Qtot hQ
    hold htail n hlo hhi
  have hb := back_run p hD extract decision H pub c1 payload prior hprior hl he Qtot hQ hold
    n hhi (n - 33) (by omega)
  rw [show 33 + (n - 33) = n by omega] at hb
  have ht := readTail_run p hD H pub c1 payload (n - 33) 33
  have hlen : (AspisRec40.FollowStatement.jointCtx p hD H pub c1 payload).records.length = 31 :=
    UnifiedRecords.records_length p hD H pub c1 payload 31
  unfold AspisRows40.Context.parse
  rw [parse_address]
  simp only [Option.bind_some, IndexedMessage.read_encoded]
  rw [hb]
  simp only [Option.bind_some]
  rw [ht]
  simp only [Option.bind_some]
  rw [hj]
  simp only [Option.bind_some, hlen, if_true]
  rfl

#print axioms table_mono
#print axioms parse_address
#print axioms joint_at
#print axioms seek_row
#print axioms back_run
#print axioms readTail_run
#print axioms context_at

end AspisRec40.FinalContext
end
