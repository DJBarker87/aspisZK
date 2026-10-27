import TxS_RawTen
import TxS_RawFinish
import TxS_RawPublic
import WAdm_Nonvacuity
import T2R_Acceptance
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_Nonvacuity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open MultiproofConeCanonical

/-- Every original transcript remains represented, with its exact public bytes,
tag and rounds, regardless of its successful/rejected execution. -/
theorem transcript_surjective (tr : RawCutTranscriptRun.ErasedPrefix) :
    ∃ raw : TxS_Carriers.Prefix, TxS_Carriers.toTyped raw=tr ∧
      raw.publicBytes=tr.statement.pubBytes ∧ raw.tag=tr.statement.tag ∧ raw.rounds=tr.rounds :=
  ⟨TxS_Carriers.erase tr,TxS_Carriers.prefix_erase tr,rfl,rfl,rfl⟩

/-- Every successful original data read and all of its input metadata survive
in the new interface. There is no honest-only choice of matching data. -/
theorem matching_input_surjective (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (i : R1FinalSoundness.SourceInputs) (read : LiteralMatchingData.read rs=some i.data) :
    ∃ m : TxS_Carriers.Metadata, TxS_Carriers.source m rs=i :=
  ⟨TxS_Carriers.eraseInput i,TxS_Carriers.source_of_read rs i read⟩

theorem failed_read_fallback (rs : LiteralAcceptanceTerminal.TranscriptRounds)
    (read : LiteralMatchingData.read rs=none) : TxS_Carriers.data rs=TxS_Carriers.zeroData := by
  rw [TxS_Carriers.data,read];rfl

theorem prefix_nonempty : Nonempty TxS_Carriers.Prefix :=
  ⟨⟨[],2,[]⟩⟩

/-- The exact local source writer domain remains inhabited. This does not
assert a jointly inhabited complete cryptographic/runtime accepted pair. -/
theorem physical_writer_domain : ∃ proof pub : Slice U8,
    WAdm_Domain.Admitted WAdm_Nonvacuity.prepared WAdm_Nonvacuity.accumulator proof pub :=
  WAdm_Nonvacuity.domain_nonempty

/-- The inherited top's source acceptance witness excludes reject-everything
under the original history/P2Prime guards; no new acceptance premise. -/
theorem accepted_source_input
    (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (H : Bytes → State) (pub proof pub2 proof2 checkpoint : Slice U8) (written : Bytes)
    (facts : T2R_Acceptance.Facts driver H pub proof pub2 proof2 checkpoint written)
    (history : S2X.CheckpointVersionBinding written (bytesOf checkpoint.val))
    (p2prime : S2W_AuthenticatedInputs.P2Prime H proof pub proof2 pub2) :
    ∃ i : OraclePortStoredExperimentC4.Input, i.statement.pubBytes=bytesOf pub.val ∧
      i.stored=bytesOf proof.val ∧ i.statement.tag=2 ∧ i.statement.pubBytes.length=1880 ∧
      (eval H (driver i)).2=true ∧ ¬ (∀ j,(eval H (driver j)).2=false) := by
  obtain ⟨i,publicBytes,stored,tag,length,fit,acceptance⟩ := facts
  exact ⟨i,publicBytes,stored,tag,length,(acceptance history p2prime).1,(acceptance history p2prime).2⟩

#print axioms transcript_surjective
#print axioms matching_input_surjective
#print axioms failed_read_fallback
#print axioms prefix_nonempty
#print axioms physical_writer_domain
#print axioms accepted_source_input
end AspisR1.TxS_Nonvacuity
end
