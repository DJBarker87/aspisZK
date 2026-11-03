import NBG_Header
import NBP_DigestDecode
import NBP_Read
set_option autoImplicit false
noncomputable section
namespace NEQ_DecodeScalar
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem header_result_state_effects {State : Type} (bytes : Array U8 216#usize)
    (magic : Array U8 4#usize) (kind : NBG_Header.K) (state : State) :
    (pool_v1.payment_relation.require_header bytes magic kind,state,([] : List Unit)) =
      (ok (NBG_Header.expected bytes magic kind),state,[]) :=
  congrArg (fun x => (x,state,([] : List Unit))) (NBG_Header.header_result bytes magic kind)

theorem m31_result_state_effects {State : Type} (bytes : Array U8 4#usize) (state : State) :
    (aspis_core.field.M31.from_le_bytes bytes,state,([] : List Unit)) =
      (ok (let word := core.num.U32.from_le_bytes bytes
        if word >= 2147483647#u32 then none else some word),state,[]) :=
  congrArg (fun x => (x,state,([] : List Unit))) (NBG_Atomic.m31_decode bytes)

theorem digest_result_state_effects {State : Type} (bytes : Array U8 32#usize) (state : State) :
    (atomic_statement.decode_digest_canonical bytes,state,([] : List Unit)) =
      (ok (NBP_DigestDecode.decoded bytes),state,[]) :=
  congrArg (fun x => (x,state,([] : List Unit))) (NBP_DigestDecode.result bytes)

/-- Every actual unrolled word call passes these exact four SAME original bytes. -/
theorem digest_word_domain (bytes : Array U8 32#usize) (i : Nat) (bound : i<8) :
    ∃ word : Array U8 4#usize,
      word.val = (bytes.val.drop (4*i)).take 4 ∧ word.val.length=4 := by
  let word : Array U8 4#usize := NBP_Read.chunk bytes (4*i) (by change 4*i+4≤32;omega)
  exact ⟨word,rfl,word.property⟩

#print axioms header_result_state_effects
#print axioms m31_result_state_effects
#print axioms digest_result_state_effects
#print axioms digest_word_domain
end NEQ_DecodeScalar
