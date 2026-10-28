import R1Z.ProverRwOuterBytes
import R1Z.ProverCommitOwnerBytes42
import R1Z.LayoutR1PBin
import R1Z.ProverCommitPublicRawBridge34
set_option autoImplicit false
namespace R1Z.ProverRwOuterContextModel
open Aeneas Aeneas.Std Result ProverRwOuterContext ProverRwOuterEncode
open ProverCommitOwnerZero42 ProverCommitOwnerBytes42

theorem block_list (b : Bytes) : b.val.map byte = LensR1.ans (block b) := by
  change b.val.map byte = List.ofFn (block b)
  refine (AspisR1PublicSerializer.RawBridge431.ofFn_map_getElem b.val 32 b.property byte).symm.trans ?_
  apply congrArg List.ofFn
  funext j
  rfl

/-- Two eight-byte constant leaves only; no seed array is evaluated. -/
theorem mask_bytes :
    (core.num.U64.to_le_bytes 18003970557850322385#u64).val.map byte =
      LayoutR1PBin.le64 LayoutR1PBin.fpMask := by
  simp [core.num.U64.to_le_bytes,byte,LayoutR1PBin.le64,LayoutR1PBin.fpMask,BitVec.toLEBytes]

theorem factor_bytes :
    (core.num.U64.to_le_bytes 7605398817818846427#u64).val.map byte =
      LayoutR1PBin.le64 LayoutR1PBin.fpFactor := by
  simp [core.num.U64.to_le_bytes,byte,LayoutR1PBin.le64,LayoutR1PBin.fpFactor,BitVec.toLEBytes]

def context (digest nonce : Bytes) : Context :=
  ⟨digest,nonce,18003970557850322385#u64,7605398817818846427#u64⟩

theorem context_encoding (digest nonce : Bytes) :
    (value (context digest nonce)).val.map byte =
      LayoutR1PBin.ctxEnc (block digest) (block nonce) := by
  rw [ProverRwOuterBytes.value_bytes]
  simp only [ProverRwOuterBytes.bytes,context,List.map_append,List.map_cons,List.map_nil,
    block_list,mask_bytes,factor_bytes,LayoutR1PBin.ctxEnc]
  rfl

theorem construct_encode (digest nonce : Bytes) :
    (do let c ← construct digest nonce
        let b ← encode c
        .ok (c,b)) = .ok (context digest nonce,value (context digest nonce)) := by
  rw [construct_fields]
  simp only [bind_tc_ok,encode_total]
  rfl

#print axioms block_list
#print axioms mask_bytes
#print axioms factor_bytes
#print axioms context_encoding
#print axioms construct_encode
end R1Z.ProverRwOuterContextModel
