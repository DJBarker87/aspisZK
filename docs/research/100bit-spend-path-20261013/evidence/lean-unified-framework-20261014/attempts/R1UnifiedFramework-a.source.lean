import R1UnifiedProtocol
import R1UnifiedVerifier
import R1UnifiedQueryRun

/-! Generic FS2 framing facts for the unified 33-row sampler: the verifier
reads every chain's first cell, and the final ordinary rho row begins at its
symbolic rho address. No probability or acceptance claim is made. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedFramework

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem readsChains (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (decision : FS.Prefix (UnifiedSampler.Public L) (Message M) (Challenge Cv) →
      Message M → Bool) :
    FS2.ReadsChains (UnifiedProtocol.protocol p hD extract)
      (fun pub π => UnifiedVerifier.verifier p hD extract decision pub π) := by
  intro H pub π i a hi ha
  apply FS2.verifier_reads (UnifiedProtocol.protocol p hD extract)
    decision H pub π i hi a
  exact R0C.V3.DQ.firstCell_mem H
    ((UnifiedProtocol.protocol p hD extract).chain H pub π i) a ha

theorem rho_firstCell (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (c1, payload) 32) =
      some (UnifiedQueryRun.rhoAddress p hD H pub c1 payload) := by
  rw [UnifiedProtocol.chain_eq]
  rw [UnifiedSampler.row_rho]
  simp [DuplexSamplers.plain, UnifiedQueryRun.rhoAddress, UnifiedSampler.absorb]

#print axioms readsChains
#print axioms rho_firstCell

end AspisR1.UnifiedFramework
end
