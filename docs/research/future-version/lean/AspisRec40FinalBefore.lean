import R1DuplexPrefixTable
import AspisRec40FinalRun

/-! Fact (a) of RECORDED-EXPERIMENT-40.md §10.2: on a trace with R1's
no-collision premise (`badColl`), the frames of rows 32 .. n-1 and the advance
cells between them are read before row n's frame, so the table before row n's
frame holds their answers.

`chain_before` is generic (any frame sequence whose next frame begins with the
advance of the previous frame's answer), proved with R1's
`noColl_prefix_after` (FS2.DuplexTrace) and `before_trans`, as R1's
`DuplexPrefixTable.before_endpoint` / `table_cells` do for the query chain.
`run_cells` instantiates it on the 40-row address-level run
(`AspisRec40.FinalRun.trace`). -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FinalBefore
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1 AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

/-- One frame step: frame `f j` is read before the advance of its answer, and
that advance before frame `f (j+1)`. -/
theorem step_before (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (a b : Addr L) (ha : Read tr a) (hadv : Read tr (advanceA p (H a))) (hb : Read tr b)
    (hpre : b.toBytes.take 32 = bytes (H (advanceA p (H a)))) :
    Before tr a (advanceA p (H a)) ∧ Before tr (advanceA p (H a)) b := by
  refine ⟨?_, ?_⟩
  · exact noColl_prefix_after p Qtot H tr hcons hQ hcoll a (advanceA p (H a)) ha hadv
      (toBytes_advanceA p (H a))
  · exact noColl_prefix_after p Qtot H tr hcons hQ hcoll (advanceA p (H a)) b hadv hb hpre

/-- A chain of frames `f k, …, f m`: every frame `f j` (k ≤ j < m) and the
advance of its answer are read before `f m`. -/
theorem chain_before (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (f : Nat → Addr L) (k : Nat)
    (hread : ∀ j, k ≤ j → Read tr (f j))
    (hadv : ∀ j, k ≤ j → Read tr (advanceA p (H (f j))))
    (hpre : ∀ j, k ≤ j → (f (j + 1)).toBytes.take 32 = bytes (H (advanceA p (H (f j))))) :
    ∀ d j, k ≤ j → Before tr (f j) (f (j + d + 1)) ∧
      Before tr (advanceA p (H (f j))) (f (j + d + 1)) := by
  intro d
  induction d with
  | zero =>
      intro j hj
      obtain ⟨h1, h2⟩ := step_before p H tr Qtot hcons hQ hcoll (f j) (f (j + 1))
        (hread j hj) (hadv j hj) (hread (j + 1) (by omega)) (hpre j hj)
      exact ⟨before_trans tr h1 h2, h2⟩
  | succ d ih =>
      intro j hj
      obtain ⟨h1, h2⟩ := ih j hj
      obtain ⟨_, h4⟩ := ih (j + d + 1) (by omega)
      have e : j + d + 1 + 0 + 1 = j + (d + 1) + 1 := by omega
      have h4' : Before tr (advanceA p (H (f (j + d + 1)))) (f (j + (d + 1) + 1)) := by
        have := (step_before p H tr Qtot hcons hQ hcoll (f (j + d + 1)) (f (j + d + 1 + 1))
          (hread _ (by omega)) (hadv _ (by omega)) (hread _ (by omega)) (hpre _ (by omega))).2
        simpa only [show j + d + 1 + 1 = j + (d + 1) + 1 by omega] using this
      have hmid : Before tr (f (j + d + 1)) (advanceA p (H (f (j + d + 1)))) :=
        (step_before p H tr Qtot hcons hQ hcoll (f (j + d + 1)) (f (j + d + 1 + 1))
          (hread _ (by omega)) (hadv _ (by omega)) (hread _ (by omega)) (hpre _ (by omega))).1
      have hchain := before_trans tr hmid h4'
      exact ⟨before_trans tr h1 hchain, before_trans tr h2 hchain⟩

/-- Fact (a) on the 40-row run: for `32 ≤ j < n < 40`, the table before row n's
frame holds row j's frame (answer: row j's absorbed state) and the advance of
that state (answer: the state before row j+1). -/
theorem run_cells (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (prior : List (Addr L × State))
    (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hl : p.lbl 0 = 160) (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hn : n < 40) (j : Nat) (hlo : 32 ≤ j) (hj : j < n) :
    let tr := AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior
    let c := UnifiedSteps.address p hD H pub c1 payload n
    Before tr (UnifiedSteps.address p hD H pub c1 payload j) c ∧
    Before tr (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload j)) c ∧
    tableBefore emptyTable tr c (UnifiedSteps.address p hD H pub c1 payload j) =
      some (UnifiedRecords.absorbed p hD H pub c1 payload j) ∧
    tableBefore emptyTable tr c (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload j)) =
      some (UnifiedRecords.previous p hD H pub c1 payload (j + 1)) := by
  intro tr c
  have hcons := AspisRec40.FinalRun.trace_consistent p hD extract decision H pub c1 payload
    prior hprior
  let f : Nat → Addr L := fun i => UnifiedSteps.address p hD H pub c1 payload (32 + i)
  have hreads (i : Nat) (hi : i < 8) :=
    AspisRec40.FinalRun.final_reads p hD extract decision H pub c1 payload prior hl he
      (32 + i) (by omega) (by omega)
  have habs (i : Nat) : H (f i) = UnifiedRecords.absorbed p hD H pub c1 payload (32 + i) := rfl
  have hprefix (i : Nat) :
      (f (i + 1)).toBytes.take 32 = bytes (H (advanceA p (H (f i)))) := by
    rw [habs]
    rw [← AspisRec40.FinalRun.final_state_step p hD H pub c1 payload hl he (32 + i) (by omega)]
    exact toBytes_absorbA p _ _ _ _
  -- restrict the chain to i < 8 by reading at a capped index
  have key : ∀ d i, i + d + 1 < 8 → Before tr (f i) (f (i + d + 1)) ∧
      Before tr (advanceA p (H (f i))) (f (i + d + 1)) := by
    intro d
    induction d with
    | zero =>
        intro i hi
        obtain ⟨h1, h2⟩ := step_before p H tr Qtot hcons hQ hcoll (f i) (f (i + 1))
          (hreads i (by omega)).1 (by rw [habs]; exact (hreads i (by omega)).2.2)
          (hreads (i + 1) (by omega)).1 (hprefix i)
        exact ⟨before_trans tr h1 h2, h2⟩
    | succ d ih =>
        intro i hi
        obtain ⟨h1, h2⟩ := ih i (by omega)
        have hs := step_before p H tr Qtot hcons hQ hcoll (f (i + d + 1)) (f (i + d + 1 + 1))
          (hreads _ (by omega)).1 (by rw [habs]; exact (hreads _ (by omega)).2.2)
          (hreads _ (by omega)).1 (hprefix _)
        have e : i + d + 1 + 1 = i + (d + 1) + 1 := by omega
        rw [e] at hs
        have hchain := before_trans tr hs.1 hs.2
        exact ⟨before_trans tr h1 hchain, before_trans tr h2 hchain⟩
  obtain ⟨hb1, hb2⟩ := key (n - j - 1) (j - 32) (by omega)
  have ej : f (j - 32) = UnifiedSteps.address p hD H pub c1 payload j := by
    show UnifiedSteps.address p hD H pub c1 payload (32 + (j - 32)) = _
    rw [show 32 + (j - 32) = j by omega]
  have en : f (j - 32 + (n - j - 1) + 1) = c := by
    show UnifiedSteps.address p hD H pub c1 payload (32 + (j - 32 + (n - j - 1) + 1)) = _
    rw [show 32 + (j - 32 + (n - j - 1) + 1) = n by omega]
  have ea : H (f (j - 32)) = UnifiedRecords.absorbed p hD H pub c1 payload j := by
    rw [ej]; rfl
  rw [en, ej] at hb1
  rw [en, ea] at hb2
  refine ⟨hb1, hb2, ?_, ?_⟩
  · rw [tableBefore_eq H tr emptyTable c _ hcons, if_pos hb1]
    rfl
  · rw [tableBefore_eq H tr emptyTable c _ hcons, if_pos hb2]
    exact congrArg some
      (AspisRec40.FinalRun.final_state_step p hD H pub c1 payload hl he j hlo).symm

#print axioms step_before
#print axioms chain_before
#print axioms run_cells

end AspisRec40.FinalBefore
end
