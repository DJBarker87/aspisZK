import NNG_ValidatorGraph345
import NMT_R2_EncoderTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_EncoderGraph345
open Aeneas Aeneas.Std NMT_345 RSL

def native (st : Statement) :=
 mapOuter (mapCore id (fun _ : EncodeError => (.InvalidAccountData : PE)))
  (encodeCall (commonValue st).lane_transition.candidate_afterstate)

def option (r : Option Bytes) : Except ProgramError Bytes :=
 match r with | some b=>.ok b | none=>.error .invalidAccountData

theorem observation (st : Statement) :
 NNG_Observe345.observe (fun a : Array U8 688#usize=>a.val.map byte) (native st)=
 NNG_Pure345.silent (option (LIBC_S1.encode st)) := by
 unfold native LIBC_S1.encode
 rw [NMT_R2_EncoderTotal.source]
 cases NMT_R2_EncoderTotal.value (commonValue st).lane_transition.candidate_afterstate <;> rfl
#print axioms observation

theorem law (st : Statement) (env : Env) :
 RS.ofOption (LIBC_S1.encode st) .invalidAccountData env
 (NNG_Observe345.observe (fun a : Array U8 688#usize=>a.val.map byte) (native st)) := by
 rw [observation]
 cases LIBC_S1.encode st <;> rfl
#print axioms law
end AspisR1.NNG_EncoderGraph345
