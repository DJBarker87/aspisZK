import JHb_DataRequest
import JGx_MagicStd
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_RequestCarrier
open Aeneas Aeneas.Std Result

def payload : Array U8 316#usize := ⟨JHb_DataRequest.bytes.drop 4,by
  rw [List.length_drop,JHb_DataRequest.length]
  rfl⟩

theorem same : JGx_RequestBytes.value payload=JHb_DataRequest.value := by
  apply Subtype.ext
  change JGx_RequestBytes.magic.val ++ JHb_DataRequest.bytes.drop 4=JHb_DataRequest.bytes
  have header : JHb_DataRequest.bytes.take 4=JGx_RequestBytes.magic.val := rfl
  rw [← header]
  exact List.take_append_drop 4 JHb_DataRequest.bytes
#print axioms same

theorem magic (base : AdapterRw.Ops) :
    JGx_MagicGate.value (JGx_MagicStd.install base) JHb_DataRequest.value=ok false := by
  rw [← same]
  exact JGx_MagicStd.source base payload
#print axioms magic

theorem length : Slice.len JHb_DataRequest.value=320#usize := by
  rw [← same]
  exact JGx_RequestBytes.length payload
#print axioms length
end AspisR1.JHb_RequestCarrier
end
