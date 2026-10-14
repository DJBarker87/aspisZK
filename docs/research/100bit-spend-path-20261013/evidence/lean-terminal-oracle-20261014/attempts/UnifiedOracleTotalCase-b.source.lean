import UnifiedOracleTrace
import R1UnifiedTotalCase
import UnifiedOracleVerifier
import R1UnifiedVerifier
import R1UnifiedProtocol
import TraceAppend
import FollowAppend

/-! Transport the existing total dispatcher across the terminal decision trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOracleTotalCase

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

private theorem firstCell_mem {I A C : Type} [DecidableEq I] [Inhabited A]
    (H : I → A) (s : FS2.Sampler I A C) (a : I)
    (ha : FS2.firstCell s = some a) :
    a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => cases ha
  | ask i k =>
      simp only [FS2.firstCell, Option.some.injEq] at ha
      subst i
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [FS2.firstCell, Option.some.injEq] at ha
      subst c
      exact List.mem_cons_self ..

theorem decodes_and_follows (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Program (Addr L) State Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32)
    (hl : ∀ n < 33, p.lbl n = UnifiedLabels.label n)
    (m0 : M) (he0 : p.enc m0 = PublicInitFrame.emptyRecord)
    (Qtot : Nat)
    (hQ : firstReads emptyTable
      (eval H (FS2.experiment prover
        (UnifiedOracleVerifier.verifier p hD extract decision) pub)).1 ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable
      (eval H (FS2.experiment prover
        (UnifiedOracleVerifier.verifier p hD extract decision) pub)).1)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable (eval H (FS2.experiment prover
        (UnifiedOracleVerifier.verifier p hD extract decision) pub)).1)
    (n : Nat) (hn : n < 33) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H prover).2 n) = some a) :
    let π := (eval H prover).2
    let tr := (eval H (FS2.experiment prover
      (UnifiedOracleVerifier.verifier p hD extract decision) pub)).1
    let T := tableBefore emptyTable tr a
    ∃ own pend g,
      UnifiedDecoder.decode p hD pub a T = some (own, pend, g) ∧
      bfollow g (traceFrom tr a) own pend T =
        some ((UnifiedProtocol.protocol p hD extract).transcript H pub π n,
          (UnifiedProtocol.protocol p hD extract).msg π n,
          (UnifiedProtocol.protocol p hD extract).chal H pub π n) := by
  dsimp only
  let π := (eval H prover).2
  let tr := (eval H (FS2.experiment prover
    (UnifiedOracleVerifier.verifier p hD extract decision) pub)).1
  let base := (eval H (FS2.experiment prover
    (UnifiedVerifier.verifier p hD extract (fun _ _ => true)) pub)).1
  let terminal := (eval H (decision
    ((UnifiedProtocol.protocol p hD extract).transcript H pub π 33)
    ((UnifiedProtocol.protocol p hD extract).msg π 33))).1
  have hsplit : tr = base ++ terminal := by
    dsimp [tr, base, terminal, π]
    exact UnifiedOracleTrace.trace_decomposition p hD extract decision prover H pub
  have hchain : a ∈ (eval H ((UnifiedProtocol.protocol p hD extract).chain H pub π n).toProgram).1.map Prod.fst :=
    firstCell_mem H ((UnifiedProtocol.protocol p hD extract).chain H pub π n) a hfirst
  have hV : a ∈ (eval H
      (UnifiedVerifier.verifier p hD extract (fun _ _ => true) pub π)).1.map Prod.fst := by
    apply FS2.verifier_reads (UnifiedProtocol.protocol p hD extract)
      (fun _ _ => true) H pub π n hn a
    exact hchain
  have hreadBase : Read base a := by
    dsimp [base, Read]
    rw [FS2.experiment_eval]
    simp only [List.map_append, List.mem_append]
    exact Or.inr hV
  have hQbase : firstReads emptyTable base ≤ Qtot := by
    rw [hsplit] at hQ
    exact le_trans (TraceAppend.firstReads_le_append emptyTable base terminal) hQ
  have holdBase : ¬ hitsBad (badColl p Qtot) emptyTable base := by
    intro hbad
    apply hold
    rw [hsplit]
    exact TraceAppend.hitsBad_of_prefix (badColl p Qtot) emptyTable base terminal hbad
  have htailBase : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable base := by
    intro hbad
    apply htail
    rw [hsplit]
    exact TraceAppend.hitsBad_of_prefix
      (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot) emptyTable base terminal hbad
  obtain ⟨own, pend, g, hdecode, hfollow⟩ :=
    UnifiedTotalCase.decodes_and_follows p hD extract (fun _ _ => true) H pub prover
      hpub hl m0 he0 Qtot hQbase holdBase htailBase n hn a hfirst
  refine ⟨own, pend, g, ?_, ?_⟩
  · rw [hsplit, TraceAppend.tableBefore_append emptyTable base terminal a hreadBase]
    exact hdecode
  · rw [hsplit, TraceAppend.traceFrom_append base terminal a hreadBase]
    exact FollowAppend.bfollow_append_of_some g (traceFrom base a) terminal own pend
      (tableBefore emptyTable base a)
      _ hfollow

#print axioms decodes_and_follows

end AspisR1.UnifiedOracleTotalCase
end
