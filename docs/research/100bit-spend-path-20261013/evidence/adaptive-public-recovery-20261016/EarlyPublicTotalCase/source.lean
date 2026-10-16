import EarlyPublicExperiment
import EarlyPublicSpecialCases
import R1UnifiedCanonicalProver

/-! Public selection for rounds 0 through 26 of an arbitrary bounded-model
prover. Existing canonical-row-zero transport removes the dummy-payload premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.EarlyPublicTotalCase
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open TranscriptView
variable {M Cv W : Type} {L : Nat}

def select (p : Params M Cv L) (a : Addr L) (T : Table (Addr L) State) :
    Option (UnifiedSampler.Public L) :=
  (EarlyPublicSelection.ordinary p a T).orElse (fun _ => EarlyPublicSelection.initial a)

theorem of_ordinary (p : Params M Cv L) (a : Addr L) (T : Table (Addr L) State)
    (pub : UnifiedSampler.Public L) (h : EarlyPublicSelection.ordinary p a T = some pub) :
    select p a T = some pub := by simp only [select,h,Option.orElse_some]

theorem at_initial (p : Params M Cv L) (pub : UnifiedSampler.Public L) (root : State)
    (hlen : pub.pubBytes.length < 2^32) (htag : pub.tag = 2) (T : Table (Addr L) State) :
    select p (PublicInitFrame.addr pub.pubBytes pub.initFits root) T = some pub := by
  have hp := PublicInitParse.parse_addr pub.pubBytes hlen pub.initFits root
  have hn := PublicInitAbsorbSeparation.parseAbsorb_none_of_init pub.pubBytes _ root hp
  unfold select EarlyPublicSelection.ordinary
  rw [hn]
  exact EarlyPublicSelection.initial_addr pub root hlen htag

theorem canonical_case (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hl : p.lbl 0 = 160) (he : p.enc ((eval H prover).2.2 0) = PublicInitFrame.emptyRecord)
    (Q : Nat)
    (hQ : firstReads emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Q)
    (hout : ¬ hitsBad (badColl p Q) emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (n : Nat) (hn : n ≤ 26) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (eval H prover).2 n) = some a) :
    select p a (tableBefore emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 a) = some pub := by
  by_cases h0 : n = 0
  · subst n
    have hi := UnifiedFramework.initial_firstCell p hD extract H pub
      (eval H prover).2.1 (eval H prover).2.2
    have ha : a = PublicInitFrame.addr pub.pubBytes pub.initFits (eval H prover).2.1 :=
      Option.some.inj (hfirst.symm.trans hi)
    rw [ha]
    exact at_initial p pub _ hpub htag _
  · apply of_ordinary
    by_cases h26 : n = 26
    · subst n
      exact EarlyPublicSpecialCases.reseed_first_cell p hD extract decision H pub prover
        hpub htag hl he Q hQ hout a hfirst
    · exact EarlyPublicExperiment.ordinary_at_first_cell p hD extract decision H pub prover
        hpub htag hl he Q hQ hout n (by omega) (by omega) a hfirst

theorem actual_first_cell (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : UnifiedSampler.Prefix M Cv L → Message M → Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (prover : Program (Addr L) State (UnifiedProtocol.Proof M))
    (hpub : pub.pubBytes.length < 2^32) (htag : pub.tag = 2)
    (hl : p.lbl 0 = 160) (m0 : M) (he0 : p.enc m0 = PublicInitFrame.emptyRecord)
    (Q : Nat)
    (hQ : firstReads emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Q)
    (hout : ¬ hitsBad (badColl p Q) emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1)
    (n : Nat) (hn : n ≤ 26) (a : Addr L)
    (hfirst : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (eval H prover).2 n) = some a) :
    select p a (tableBefore emptyTable (eval H (FS.experiment prover
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 a) = some pub := by
  let canon := UnifiedCanonicalProver.prover m0 prover
  have htrace : (eval H (FS.experiment canon
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 =
      (eval H (FS.experiment prover
        (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 := by
    rw [FS.experiment_eval, FS.experiment_eval, UnifiedCanonicalProver.eval_prover]
    rw [UnifiedPayloadZero.verifier_eq p hD extract decision pub (eval H prover).2 m0]
  have hfirstCanon : firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H canon).2 n) = some a := by
    change firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub
      (eval H (UnifiedCanonicalProver.prover m0 prover)).2 n) = some a
    rw [UnifiedCanonicalProver.eval_prover,UnifiedPayloadZero.protocol_chain_eq]
    exact hfirst
  have hqc : firstReads emptyTable (eval H (FS.experiment canon
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 ≤ Q := by
    rw [htrace]
    exact hQ
  have hoc : ¬ hitsBad (badColl p Q) emptyTable (eval H (FS.experiment canon
      (fun x pf => UnifiedVerifier.verifier p hD extract decision x pf) pub)).1 := by
    rw [htrace]
    exact hout
  have hc := canonical_case p hD extract decision H pub canon hpub htag hl
    (UnifiedCanonicalProver.codec p H m0 prover he0) Q hqc hoc n hn a hfirstCanon
  rw [htrace] at hc
  exact hc

#print axioms canonical_case
#print axioms actual_first_cell
end AspisR1.EarlyPublicTotalCase
end
