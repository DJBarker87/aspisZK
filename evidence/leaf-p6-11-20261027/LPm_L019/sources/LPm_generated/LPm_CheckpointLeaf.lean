import LPm_FieldCarriers
import LPm_CheckpointWitness
import CheckpointBytes5Join
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPm_CheckpointLeaf
open Aeneas Aeneas.Std Result
open CheckpointBytes5Effect CheckpointBytes5Writer CheckpointBytes5Inputs
open CheckpointBytes5Join CheckpointBytesDigest
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Concrete checkpoint leaf carrier join under the EXISTING caller-state
domain. No new independent p/a inventory, output equality, digest trace or
accepted run is a hypothesis. The local trace's construction is exactly the
native per-step/source association in the LPm closure packet. -/
theorem native_result {Hash : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (p : Prepared) (a : Accumulator) (proof public1 : Slice U8)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (provenance : S1S7S8StateProvenance p a pm am)
    (hp hu hc : Digest) (body out : Slice U8) (before : Log)
    (tr : LPm_CheckpointTrace.Trace p a provenance.size provenance.queriesBound hp hu hc body out)
    (proofCall : D.digest hash (singletonParts proof) = ok hp)
    (publicCall : D.digest hash (singletonParts public1) = ok hu)
    (checksumCall : D.digest hash (checksumParts body) = ok hc) :
    erase D hash (writer p a proof public1) = ok out ∧
    run D hash (writer p a proof public1) before =
      ok (out,((before ++ [(singletonParts proof,hp)]) ++
        [(singletonParts public1,hu)]) ++ [(checksumParts body,hc)]) := by
  have joined := LPm_CheckpointTrace.native_result D hash p a proof public1
    provenance.size provenance.queriesBound provenance.canonical provenance.next
    hp hu hc body out before tr proofCall publicCall checksumCall
  exact ⟨run_success D hash _ _ _ _ joined,joined⟩

#print axioms native_result
end AspisR1.LPm_CheckpointLeaf
end
