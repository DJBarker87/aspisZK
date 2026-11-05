import NGX_SemanticDomain
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NGX_SemanticNew
abbrev Bytes32 := Array U8 32#usize

def parts (publicBytes : Slice U8) (root : Bytes32) (length : U32) : Slice (Slice U8) :=
 Array.to_slice (Array.make 5#usize [r1_wire.DOMAIN,
  Array.to_slice (Array.make 1#usize [0#u8]),
  Array.to_slice (core.num.U32.to_le_bytes length),publicBytes,Array.to_slice root])

def computation {H : Type} (D : aspis_core.Digest32 H) (hash : H)
 (publicBytes : Slice U8) (root : Bytes32) :
 Result (core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error) := do
 let converted ← core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len publicBytes)
 match converted with
 | .Err _ => ok (.Err .Public)
 | .Ok length => do
   let reply ← D.digest hash (parts publicBytes root length)
   ok (.Ok {state:=reply,hash,next_row:=0#u8})

theorem source {H : Type} (D : aspis_core.Digest32 H) (hash : H)
 (publicBytes : Slice U8) (root : Bytes32) :
 r1_wire.SemanticTranscript.new D hash publicBytes root = computation D hash publicBytes root := by
 unfold r1_wire.SemanticTranscript.new computation
 cases h : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len publicBytes) <;>
   simp only [h,bind_tc_fail,bind_tc_div,bind_tc_ok]
 rename_i converted
 cases converted <;> rfl

theorem length_success (length : Usize) (bound : length.val ≤ 4294967295) :
 core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from length =
  ok (.Ok (UScalar.cast .U32 length)) := by
 unfold core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from core.num.tryFromUScalar
 rw [if_pos]
 scalar_tac

theorem length_error (length : Usize) (bound : 4294967295 < length.val) :
 core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from length = ok (.Err ()) := by
 unfold core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from core.num.tryFromUScalar
 rw [if_neg]
 scalar_tac

theorem returned {H : Type} (D : aspis_core.Digest32 H) (hash : H)
 (publicBytes : Slice U8) (root reply : Bytes32)
 (bound : (Slice.len publicBytes).val ≤ 4294967295)
 (digest : D.digest hash (parts publicBytes root (UScalar.cast .U32 (Slice.len publicBytes)))=ok reply) :
 r1_wire.SemanticTranscript.new D hash publicBytes root =
   ok (.Ok {state:=reply,hash,next_row:=0#u8}) := by
 rw [source]
 unfold computation
 rw [length_success _ bound,bind_tc_ok]
 dsimp only
 rw [digest,bind_tc_ok]

theorem rejected {H : Type} (D : aspis_core.Digest32 H) (hash : H)
 (publicBytes : Slice U8) (root : Bytes32)
 (bound : 4294967295 < (Slice.len publicBytes).val) :
 r1_wire.SemanticTranscript.new D hash publicBytes root=ok (.Err .Public) := by
 rw [source]
 unfold computation
 rw [length_error _ bound,bind_tc_ok]

#print axioms source
#print axioms length_success
#print axioms length_error
#print axioms returned
#print axioms rejected
end AspisR1.NGX_SemanticNew
