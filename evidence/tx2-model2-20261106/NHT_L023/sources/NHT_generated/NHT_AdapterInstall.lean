import NHT_Tx2AuthModel
import VTop_Entry
set_option autoImplicit false
noncomputable section
namespace NHT_AdapterInstall
open Aeneas Aeneas.Std Result
/-- Install the fresh authenticated body in the actual adapter model slot.
No change to the TX1 slot or the digest/error runtime slots. -/
def install (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) : AdapterRw.Ops :=
 {adapter with op11 := NHT_EmittedAuth.tx2_authenticated (NHT_Tx2CommonModel.constants stage)}

theorem slot (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
 (install adapter stage).op11 =
 NHT_EmittedAuth.tx2_authenticated (NHT_Tx2CommonModel.constants stage) := rfl

theorem cohort_slot (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
 (install adapter stage).op11 =
 VTop_Stages.verifier.candidate.tx2_authenticated (NHT_Tx2CommonModel.constants stage) := by
 funext H D pub proof checkpoint hash obs
 exact NHT_Tx2AuthModel.source stage D pub proof checkpoint hash obs

theorem digest_error_frame (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
 (install adapter stage).op43=adapter.op43 ∧ (install adapter stage).op44=adapter.op44 := ⟨rfl,rfl⟩
#print axioms slot
#print axioms cohort_slot
#print axioms digest_error_frame
end NHT_AdapterInstall
