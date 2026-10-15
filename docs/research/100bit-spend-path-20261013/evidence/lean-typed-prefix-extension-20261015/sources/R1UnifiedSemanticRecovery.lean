import R1UnifiedSemanticRecords
import R1UnifiedPrefixedReads
import R1InitialWalkTrace

/-! Recover the typed ordinary semantic prefix before a later ordinary row.
The parser walk, whole-trace reads, and record codec are composed without
assuming successful parsing or adding a parsed-tail collision condition. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticRecovery

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

def typed (p : Params M Cv L) (pubBytes : Bytes) (T : Table (Addr L) State)
    (fuel : Nat) (endpoint : State) : Option (State × List (Rec M)) :=
  (InitialWalk.walk p pubBytes T fuel endpoint).bind fun (c1, raw) =>
    (RawRoundDecode.decode p 0 raw).map fun rs => (c1, rs)

theorem typed_before_row (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)) (hprior : ∀ q ∈ prior, q.2 = H q.1)
    (hpub : pub.pubBytes.length < 2^32)
    (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior) ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior))
    (n : Nat) (hn : 0 < n) (hn26 : n ≤ 26) :
    let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
    let c := UnifiedSteps.address p hD H pub c1 payload n
    let T := tableBefore emptyTable tr c
    typed p pub.pubBytes T 27 (UnifiedRecords.previous p hD H pub c1 payload n) =
      some (c1, UnifiedRecords.records p hD H pub c1 payload n) := by
  let tr := UnifiedPrefixedReads.trace p hD extract decision H pub c1 payload prior
  let c := UnifiedSteps.address p hD H pub c1 payload n
  let T := tableBefore emptyTable tr c
  have hcons : ∀ q ∈ tr, q.2 = H q.1 :=
    UnifiedPrefixedReads.trace_consistent p hD extract decision H pub c1 payload prior hprior
  have hL : 75 + pub.pubBytes.length ≤ L := pub.initFits
  have hroot : UnifiedRecords.previous p hD H pub c1 payload 0 =
      H (PublicInitFrame.addr pub.pubBytes hL c1) := rfl
  have hi : Read tr (PublicInitFrame.addr pub.pubBytes hL c1) :=
    UnifiedPrefixedReads.initial_read p hD extract decision H pub c1 payload prior
  have habs : ∀ j < n, UnifiedRecords.absorbed p hD H pub c1 payload j =
      H (absorbA p (UnifiedRecords.previous p hD H pub c1 payload j)
        (p.lbl j) (p.enc (payload j)) (p.encLen (payload j))) := by
    intro j hj
    rfl
  have hstep : ∀ j < n, UnifiedRecords.previous p hD H pub c1 payload (j + 1) =
      H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload j)) := by
    intro j hj
    rw [UnifiedPhases.previous_state p hD H pub c1 payload (j + 1) (by omega)]
    exact UnifiedSteps.state_step p hD H pub c1 payload hl he j (by omega) (by omega)
  have hDdata : ∀ j, (p.enc (payload j)).length ≤ p.D := fun j => p.encLen (payload j)
  have har : ∀ j < n, Read tr
      (absorbA p (UnifiedRecords.previous p hD H pub c1 payload j)
        (p.lbl j) (p.enc (payload j)) (p.encLen (payload j))) := by
    intro j hj
    have hr := UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
      prior hl he j (by omega) (by omega)
    change absorbA p (UnifiedRecords.previous p hD H pub c1 payload j)
      (p.lbl j) (p.enc (payload j)) (p.encLen (payload j)) ∈ tr.map Prod.fst
    simpa only [UnifiedSteps.address] using hr.1
  have hdr : ∀ j < n, Read tr
      (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload j)) := by
    intro j hj
    exact (UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
      prior hl he j (by omega) (by omega)).2.2
  have hc : Read tr c := by
    exact (UnifiedPrefixedReads.ordinary_reads p hD extract decision H pub c1 payload
      prior hl he n (by omega) (by omega)).1
  have hp : c.toBytes.take 32 =
      bytes (UnifiedRecords.previous p hD H pub c1 payload n) := by
    dsimp [c, UnifiedSteps.address]
    exact toBytes_absorbA p _ _ _ _
  have hw := InitialWalkTrace.walk_before_next p pub.pubBytes hpub hL c1 H tr Qtot
    hcons hQ hold 27 n hn (by omega)
    (UnifiedRecords.previous p hD H pub c1 payload)
    (UnifiedRecords.absorbed p hD H pub c1 payload) p.lbl
    (fun j => p.enc (payload j)) hDdata hroot hi habs hstep har hdr c hc hp
  change typed p pub.pubBytes T 27
    (UnifiedRecords.previous p hD H pub c1 payload n) =
      some (c1, UnifiedRecords.records p hD H pub c1 payload n)
  unfold typed
  rw [show InitialWalk.walk p pub.pubBytes T 27
      (UnifiedRecords.previous p hD H pub c1 payload n) =
      some (c1, InitialWalk.records (UnifiedRecords.previous p hD H pub c1 payload)
        (UnifiedRecords.absorbed p hD H pub c1 payload) p.lbl
        (fun j => p.enc (payload j)) n) from hw]
  simp only [Option.bind_some]
  rw [RawRoundCompletion.decode_records, UnifiedSemanticRecords.records_eq]
  rfl

#print axioms typed_before_row

end AspisR1.UnifiedSemanticRecovery
end
