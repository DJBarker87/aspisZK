import NDO_JGk_TX2_SiblingLaws
import MultiproofConeRead32
import MultiproofConeSlices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_ReadCell
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem source (nodes : Slice U8) (cell : Nat) (start finish : Usize)
    (hs : start.val=32*cell) (hf : finish.val=32*cell+32)
    (bound : finish.val≤nodes.val.length) :
    reference.read32 (MultiproofConeSlices.sub nodes start finish)=
      ok (encodeState (JGh_TX2_NodeViews.readCell nodes cell)) := by
  have order : start.val≤finish.val := by omega
  have len : (MultiproofConeSlices.sub nodes start finish).val.length=32 := by
    rw [MultiproofConeSlices.sub_length nodes start finish order bound];omega
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub nodes start finish) (by omega)
  have selected : (nodes.val.drop (32*cell)).take 32=chunk.val := by
    rw [List.take_of_length_le (by omega)] at bytes
    simpa only [MultiproofConeSlices.sub,hs,hf,Nat.add_sub_cancel_left] using bytes.symm
  have decoded := JGh_TX2_NodeViews.read_selected nodes cell chunk selected
  rw [decoded,array_roundtrip]
  exact run
#print axioms source
end AspisR1.JGm_TX2_ReadCell
end
