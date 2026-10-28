import NBG_WideBytes
import NBG_Atomic
set_option autoImplicit false
noncomputable section
namespace NBG_AtomicDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

def decoded (bytes : Array U8 32#usize) :
    core.result.Result (Array U32 8#usize) atomic_statement.AtomicStatementError :=
  let a := NBG_WideBytes.word bytes 0; let b := NBG_WideBytes.word bytes 1
  let c := NBG_WideBytes.word bytes 2; let d := NBG_WideBytes.word bytes 3
  let e := NBG_WideBytes.word bytes 4; let f := NBG_WideBytes.word bytes 5
  let g := NBG_WideBytes.word bytes 6; let h := NBG_WideBytes.word bytes 7
  if a >= 2147483647#u32 ∨ b >= 2147483647#u32 ∨ c >= 2147483647#u32 ∨
    d >= 2147483647#u32 ∨ e >= 2147483647#u32 ∨ f >= 2147483647#u32 ∨
    g >= 2147483647#u32 ∨ h >= 2147483647#u32
  then .Err .NonCanonicalDigest
  else .Ok (NBG_WideBytes.limbs bytes)

/-- Complete error or success result for arbitrary32-byte input. -/
theorem decode_result (bytes : Array U8 32#usize) :
    atomic_statement.decode_digest_canonical bytes = ok (decoded bytes) := by
  simp [atomic_statement.decode_digest_canonical,aspis_core.field.M31.from_le_bytes,
    aspis_core.field.P,Array.index_usize,Array.length,bytes.property,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,lift,bind_tc_ok,decoded,NBG_WideBytes.limbs,NBG_WideBytes.word]
  repeat' split
  all_goals simp_all <;> omega

#print axioms decode_result
end NBG_AtomicDecode
