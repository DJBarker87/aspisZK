import NDO_JHe_Natives
import NDO_JHc_CorrectedOwnership
import JGx_EntryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_SdkReads
open Aeneas Aeneas.Std Result S2W_D189Entry
attribute [local irreducible] JHb_Header.account JFx_NativeBytes.publicInput
abbrev e := JHb_World.e1
abbrev checkpoint := CPH_FixtureData.zeros 1768 (by decide)

theorem checkpoint_buffer : e.buffers (e.handles 2).1=checkpoint := rfl
#print axioms checkpoint_buffer

theorem proof (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (JHe_Natives.sdk base stage)
      (e.snapshot 0 58295 58295)=ok (.Ok JHb_Header.account) := by
  have h := JGx_EntryReads.data (JHe_Natives.sdk base stage) e 0 58295 58295
    (Or.inl (by rw [JHb_WorldBytes.inputs.1];exact JHb_Header.length))
  rw [JHb_WorldBytes.inputs.1] at h
  exact h
#print axioms proof

theorem publicLength : JFx_NativeBytes.publicInput.val.length=1880 := by
  unfold JFx_NativeBytes.publicInput
  exact JFx_NativeBytes.publicBytes_length
#print axioms publicLength

theorem publicInput (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (JHe_Natives.sdk base stage)
      (e.snapshot 1 1880 1880)=ok (.Ok JFx_NativeBytes.publicInput) := by
  have h := JGx_EntryReads.data (JHe_Natives.sdk base stage) e 1 1880 1880
    (Or.inl (by rw [JHb_WorldBytes.inputs.2.2.1];exact publicLength))
  rw [JHb_WorldBytes.inputs.2.2.1] at h
  exact h
#print axioms publicInput

theorem checkpoint_read (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (JHe_Natives.sdk base stage)
      (e.snapshot 2 1768 1768)=ok (.Ok checkpoint) := by
  have size : (e.buffers (e.handles 2).1).val.length=1768 := by
    rw [checkpoint_buffer]
    exact List.length_replicate
  have h := JGx_EntryReads.data (JHe_Natives.sdk base stage) e 2 1768 1768 (Or.inl size)
  rw [checkpoint_buffer] at h
  exact h
#print axioms checkpoint_read

theorem length : (e.snapshot 2 1768 1768).length=.Ok 1768#usize := by
  change core.result.Result.Ok (Slice.len (e.buffers (e.handles 2).1))=_
  rw [checkpoint_buffer]
  have h : Slice.len checkpoint=1768#usize := by
    apply UScalar.eq_of_val_eq
    exact List.length_replicate
  exact congrArg core.result.Result.Ok h
#print axioms length
end AspisR1.JHe_SdkReads
end
