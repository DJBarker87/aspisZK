import R1Z.PV_L2_F3FullRetry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3AttemptSource
open R1Z.ProverCommitSourceDecoder R1Z.PV_L2_F3FullSource
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
abbrev History := List (List UInt8 × R0Z.FsStatement.OracleAnswer)

/-- The source prefixes are produced by the extracted next/owned decoder,
not arbitrary lists supplied by an observation-equality hypothesis.
Native L1/ROM association of the supplied carrier remains explicit. -/
def attempt {Proof : Type} (input : Inputs)
    (l1 : SideChannelL1AttemptRecord.Attempt Proof) (rom : History) :
    PV_L2_F3FullRetry.Attempt Proof :=
  let source := pair (K := K) input
  ⟨l1,source.2.1,source.2.2,rom⟩

theorem source_projection {Proof : Type} (input : Inputs)
    (l1 : SideChannelL1AttemptRecord.Attempt Proof) (rom : History) :
    (pair (K := K) input).1.map (PV_L2_F3Tape.outputEquiv (K := K)) =
      PV_L2_F3SourceJoint.sourceObserved (K := K) input ∧
    (attempt (K := K) input l1 rom).l1 = l1 ∧
    (attempt (K := K) input l1 rom).maskReads = (pair (K := K) input).2.1 ∧
    (attempt (K := K) input l1 rom).entropyReads = (pair (K := K) input).2.2 ∧
    (attempt (K := K) input l1 rom).rom = rom := by
  exact ⟨observed_erases input,rfl,rfl,rfl,rfl⟩

theorem owned_projection (input : Inputs) :
    ((pair (K := K) input).1.map (PV_L2_F3Tape.outputEquiv (K := K))).map Prod.fst =
      (ProverCommitOwnedDecoder.decoder (K := K) input.1 input.2).map
        ProverCommitTapeCompletion.project := by
  rw [observed_erases,PV_L2_F3SourceJoint.source_owned]

def owner {State Proof : Type}
    (next : Nat → State →
      (Inputs × SideChannelL1AttemptRecord.Attempt Proof × History) × State) :
    PV_L2_F3FullRetry.Owner State Proof := fun index state =>
  let (data,after) := next index state
  (attempt (K := K) data.1 data.2.1 data.2.2,after)

theorem complete_l1 {State Proof : Type}
    (next : Nat → State →
      (Inputs × SideChannelL1AttemptRecord.Attempt Proof × History) × State)
    (fuel index : Nat) (state : State) :
    (PV_L2_F3FullRetry.erase (PV_L2_F3FullRetry.run (owner (K := K) next) fuel index state).1,
      (PV_L2_F3FullRetry.run (owner (K := K) next) fuel index state).2) =
      SideChannelL1AttemptRecord.run
        (fun index state => let (data,after) := next index state; (data.2.1,after))
        fuel index state :=
  PV_L2_F3FullRetry.full_l1_erases (owner (K := K) next) fuel index state

#print axioms source_projection
#print axioms owned_projection
#print axioms complete_l1
end R1Z.PV_L2_F3AttemptSource
