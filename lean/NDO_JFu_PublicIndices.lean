import NDO_JFu_PublicMeta04
import NDO_JFu_PublicMeta05
import NDO_JFu_PublicMeta06
set_option autoImplicit false
namespace AspisR1.JFu_PublicIndices
open Aeneas Aeneas.Std Result

def before : Array U8 8#usize := Array.make 8#usize [13#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
def after : Array U8 8#usize := Array.make 8#usize [14#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

theorem sequence_bytes : (JFx_NativeBytes.publicInput.val.drop 288).take 8=before.val :=
  JFu_PublicMeta04.selected

theorem index_bytes : (JFx_NativeBytes.publicInput.val.drop 296).take 8=before.val :=
  JFu_PublicMeta05.selected

theorem next_bytes : (JFx_NativeBytes.publicInput.val.drop 984).take 8=after.val := by
  have selected:=congrArg (fun xs : List U8 => (xs.drop 8).take 8) JFu_PublicMeta06.selected
  rw [JFu_PublicRange.nested _ 976 16 8 8 (by decide)] at selected
  exact selected

theorem sequence : core.num.U64.from_le_bytes before=13#u64 := by rfl
theorem next : core.num.U64.from_le_bytes after=14#u64 := by rfl

theorem advance : U64.checked_add (core.num.U64.from_le_bytes before) 1#u64=
    some (core.num.U64.from_le_bytes after) := by
  rw [sequence,next]
  rfl

#print axioms sequence_bytes
#print axioms index_bytes
#print axioms next_bytes
#print axioms sequence
#print axioms next
#print axioms advance
end AspisR1.JFu_PublicIndices
