import R1UnifiedFramework
import R1UnifiedSteps

/-! Identify the first cell of an ordinary payload row. This only concerns
the sampler's address and does not claim decoder dispatch or security. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOrdinaryFirstCell

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem firstCell_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) (n : Nat)
    (hn0 : n ≠ 0) (hn26 : n ≠ 26) (hn31 : n ≠ 31) :
    firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (c1, payload) n) =
      some (UnifiedSteps.address p hD H pub c1 payload n) := by
  rw [UnifiedProtocol.chain_eq]
  have hm : UnifiedRun.message c1 payload n = .payload (payload n) := by
    cases n with
    | zero => contradiction
    | succ j => rfl
  rw [hm, UnifiedSampler.row_ordinary p hD n hn0 hn26 hn31]
  change some (UnifiedSampler.absorb p n
    (UnifiedRun.transcript p hD H pub c1 payload n) (payload n)) = _
  rw [UnifiedSteps.payload_address p hD H pub c1 payload n hn0]

#print axioms firstCell_eq

end AspisR1.UnifiedOrdinaryFirstCell
end
