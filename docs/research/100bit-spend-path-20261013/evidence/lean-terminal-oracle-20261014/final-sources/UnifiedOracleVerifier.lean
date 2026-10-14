import R1OracleVerifier
import R1UnifiedProtocol
import R1UnifiedVerifier

/-! An oracle-reading decision wrapper for the unified protocol. These are
verifier specialization and trace facts only; no decision procedure or
acceptance premises are selected here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOracleVerifier

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

def verifier (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Program (Addr L) State Bool)
    (pub : UnifiedSampler.Public L) (π : UnifiedProtocol.Proof M) :
    Program (Addr L) State Bool :=
  OracleVerifier.verifier (UnifiedProtocol.protocol p hD extract) decision pub π

theorem specializes_done (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool)
    (pub : UnifiedSampler.Public L) (π : UnifiedProtocol.Proof M) :
    verifier p hD extract (fun P msg => Program.done (decision P msg)) pub π =
      UnifiedVerifier.verifier p hD extract decision pub π := by
  unfold verifier UnifiedVerifier.verifier
  exact OracleVerifier.verifier_specializes_done
    (UnifiedProtocol.protocol p hD extract) decision pub π

private theorem firstCell_mem {I A C : Type} [DecidableEq I] [Inhabited A]
    (H : I → A) (s : Sampler I A C) (a : I) (ha : firstCell s = some a) :
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

theorem readsChains (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Program (Addr L) State Bool) :
    FS2.ReadsChains (UnifiedProtocol.protocol p hD extract)
      (fun pub π => verifier p hD extract decision pub π) := by
  intro H pub π i a hi ha
  apply OracleVerifier.verifier_chain_reads
    (UnifiedProtocol.protocol p hD extract) decision H pub π i hi a
  exact firstCell_mem H
    ((UnifiedProtocol.protocol p hD extract).chain H pub π i) a ha

theorem verifier_eval (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Program (Addr L) State Bool)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (π : UnifiedProtocol.Proof M) :
    eval H (verifier p hD extract decision pub π) =
      (((List.range 33).map fun j =>
          (eval H ((UnifiedProtocol.protocol p hD extract).chain H pub π j).toProgram).1).flatten ++
        (eval H (decision
          ((UnifiedProtocol.protocol p hD extract).transcript H pub π 33)
          ((UnifiedProtocol.protocol p hD extract).msg π 33))).1,
        (eval H (decision
          ((UnifiedProtocol.protocol p hD extract).transcript H pub π 33)
          ((UnifiedProtocol.protocol p hD extract).msg π 33))).2) := by
  simpa [verifier, UnifiedProtocol.protocol] using
    (OracleVerifier.verifier_eval (UnifiedProtocol.protocol p hD extract)
      decision H pub π)

#print axioms specializes_done
#print axioms readsChains
#print axioms verifier_eval

end AspisR1.UnifiedOracleVerifier
end
