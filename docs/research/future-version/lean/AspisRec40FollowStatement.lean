import R1UnifiedRhoInjection
import AspisRec40FinalRun
import AspisRows40Final

/-! The follow for the final component, STATED (no proof in this file; the
statement is a `def … : Prop`, so nothing is assumed).

Copy of the follow half of R1's `UnifiedRhoInjection.decodes_and_follows`
(row 32; from `OpeningQueryTrace.recover_and_follow` /
`JointNextTrace.follows_after_prefix_query`) for rows 33 to 39, with R1's
premises unchanged: prior reads consistent with the oracle, the public
length, the row-0 codec, the first-read budget `Qtot`, and R1's two collision
exclusions `badColl p Qtot` and `ParsedStateCollision.bad tailState Qtot`.

`actualCtx`: the context the parser must recover from row n's frame on the
actual run (R1's row-32 context, row 32's frame, the frames and messages of
rows 33..n-1, the state after row n-1, row n's message). The conclusion: the
final component's background output, followed along the trace from the FIRST
occurrence of row n's frame, at the table before it, is the actual prefix,
message and challenge of row n. The first occurrence may be the prover's
(`prior`), so the squeeze cells of rows 32..n-1 and R1's pending cells may be
absent from the table; they are the pending answers. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.FollowStatement
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1 AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

/-- R1's actual row-32 context (as in `UnifiedRhoInjection`). -/
def jointCtx (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
    (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M) :
    JointContext.Context M L :=
  ⟨(UnifiedQueryRun.queryResult p hD H pub c1 payload).2,
    UnifiedQueryRun.queryAddress p hD H pub c1 payload, c1,
    UnifiedRecords.records p hD H pub c1 payload 31, payload 31, payload 32⟩

/-- The actual context of row n (33 ≤ n < 40). -/
def actualCtx (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
    (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M) (n : Nat) :
    AspisRows40.Context.Context M L :=
  ⟨jointCtx p hD H pub c1 payload, UnifiedSteps.address p hD H pub c1 payload 32,
    (List.range (n - 33)).map (fun j =>
      (UnifiedSteps.address p hD H pub c1 payload (33 + j), payload (33 + j))),
    UnifiedRecords.previous p hD H pub c1 payload n, payload n⟩

/-- The follow claim for rows 33 to 39, with R1's premises. -/
def FollowClaim (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) → Message M → Bool) :
    Prop :=
  ∀ (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)
    (prior : List (Addr L × State)), (∀ q ∈ prior, q.2 = H q.1) →
    pub.pubBytes.length < 2^32 →
    p.lbl 0 = 160 → p.enc (payload 0) = PublicInitFrame.emptyRecord →
    ∀ (Qtot : Nat),
    firstReads emptyTable (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior) ≤ Qtot →
    ¬ hitsBad (badColl p Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior) →
    ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot) emptyTable
      (AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior) →
    ∀ (n : Nat), 33 ≤ n → n < 40 →
      let tr := AspisRec40.FinalRun.trace p hD extract decision H pub c1 payload prior
      let c := UnifiedSteps.address p hD H pub c1 payload n
      let T := tableBefore emptyTable tr c
      let ctx := actualCtx p hD H pub c1 payload n
      bfollow (AspisRows40.Final.output p pub T n ctx) (traceFrom tr c) (QueryNextLaw.own p c)
          ((AspisRows40.Final.missing p T ctx).map fun b => (b, none)) T =
        some (UnifiedRun.transcript p hD H pub c1 payload n,
          UnifiedRun.message c1 payload n,
          UnifiedRun.challenge p hD H pub c1 payload n)

end AspisRec40.FollowStatement
end
