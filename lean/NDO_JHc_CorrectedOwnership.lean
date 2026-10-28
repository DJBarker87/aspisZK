import NDO_JHb_WorldBytes
import Hist_Metadata
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_CorrectedOwnership
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers

/-- Ownership and privileges on JHb's corrected common TX1 bank tuple. -/
theorem readonly_guards :
    AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
      (JHb_World.e1.snapshot 0 58295 58295)=ok (.Ok ()) ∧
    AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
      (JHb_World.e1.snapshot 1 1880 1880)=ok (.Ok ()) := ⟨rfl,rfl⟩
#print axioms readonly_guards

theorem checkpoint_same :
    JHb_World.e1.snapshot 2 1768 1768=
      (JFv_World.e1 JHb_Header.account).snapshot 2 1768 1768 := rfl
#print axioms checkpoint_same

theorem checkpoint_owner :
    (JHb_World.e1.snapshot 2 1768 1768).owner=CPH_Program.verifier := rfl
#print axioms checkpoint_owner

theorem raw_owner :
    (JHb_World.e1.snapshot 0 58295 58295).owner=JHb_Programs.foreign ∧
    (JHb_World.e1.snapshot 1 1880 1880).owner=JHb_Programs.foreign := ⟨rfl,rfl⟩
#print axioms raw_owner

/-- The corrected physical raw inputs select exactly the existing verifier
fixture inputs, without selecting another preparation or checkpoint. -/
theorem inputs :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (JHb_World.e1.buffers (JHb_World.e1.handles 0).1)
      {start:=688#usize,«end»:=58295#usize}=ok JFx_NativeBytes.proof ∧
    JHb_World.e1.buffers (JHb_World.e1.handles 1).1=JFx_NativeBytes.publicInput := by
  rw [JHb_WorldBytes.inputs.1,JHb_WorldBytes.inputs.2.2.1]
  exact ⟨JHb_Header.suffix,rfl⟩
#print axioms inputs
end AspisR1.JHc_CorrectedOwnership
end
