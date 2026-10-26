import TxS_Carriers
import T2R_Public
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_RawPublic
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames
open MultiproofConeCanonical

def Facts (pub proof : Slice U8) : Prop :=
  ∃ i : OraclePortStoredExperimentC4.Input,
    i.statement.pubBytes=bytesOf pub.val ∧ i.stored=bytesOf proof.val ∧
    i.statement.tag=2 ∧ i.statement.pubBytes.length=1880 ∧
    75+i.statement.pubBytes.length≤SelectedTranscriptParams.L ∧
    ∀ raw : TxS_Carriers.Prefix, raw.publicBytes=bytesOf pub.val →
      75+raw.publicBytes.length≤SelectedTranscriptParams.L

theorem of_typed (pub proof : Slice U8) (old : T2R_Public.Facts pub proof) : Facts pub proof := by
  obtain ⟨i,pubEq,stored,tag,length,fit,rest⟩ := old
  refine ⟨i,pubEq,stored,tag,length,fit,?_⟩
  intro raw same
  rw [same,← pubEq]
  exact fit

theorem to_typed (pub proof : Slice U8) (new : Facts pub proof) : T2R_Public.Facts pub proof := by
  obtain ⟨i,pubEq,stored,tag,length,fit,rest⟩ := new
  refine ⟨i,pubEq,stored,tag,length,fit,?_⟩
  intro tr same
  exact rest (TxS_Carriers.erase tr) same

#print axioms of_typed
#print axioms to_typed
end AspisR1.TxS_RawPublic
end
