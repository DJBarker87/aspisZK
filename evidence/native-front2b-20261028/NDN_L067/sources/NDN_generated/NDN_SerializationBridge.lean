import NDN_Reference12.Funs
import NDN_Reference13.Funs
import NDN_Reference14.Funs
import NDN_Reference18.Funs
import NDE_RowBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDN_SerializationBridge

theorem canonical (w : U32) :
 NDN_Reference14.field_canonical w=ok (decide (w.val<2147483647)) := rfl

theorem byte (w : U32) (i : Usize) :
 NDN_Reference13.field_byte w i=Array.index_usize (core.num.U32.to_le_bytes w) i := rfl

theorem byte_total (w : U32) (i : Usize) (hi:i.val<4) :
 ∃ b,NDN_Reference13.field_byte w i=ok b := by
 obtain ⟨b,hb,_⟩ := NDE_RowBridge.read_total (core.num.U32.to_le_bytes w) i hi
 exact ⟨b,(byte w i).trans hb⟩

theorem canonical_word (w : U32) (hw:w.val<2147483647) :
 NDN_Reference12.fields_word w=ok (.Ok (core.num.U32.to_le_bytes w)) := by
 have h : ¬ w≥2147483647#u32 := by scalar_tac
 simp only [NDN_Reference12.fields_word,if_neg h,lift,bind_tc_ok]

theorem rejected_word (w : U32) (hw:2147483647≤w.val) :
 NDN_Reference12.fields_word w=ok (.Err 0#u8) := by
 have h : w≥2147483647#u32 := by scalar_tac
 simp only [NDN_Reference12.fields_word,if_pos h]

theorem preserved_prefix (i n : Usize) :
 NDN_Reference18.prefix_survives i n=ok (decide (i.val<n.val)) := rfl

#print axioms canonical
#print axioms byte
#print axioms byte_total
#print axioms canonical_word
#print axioms rejected_word
#print axioms preserved_prefix
end NDN_SerializationBridge
