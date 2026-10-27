import WAdm_VecStd
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_EmittedScalars
open WAdm_Fissioned WAdm_model
open OraclePortCkptAbi2Extracted
abbrev K := OraclePortCkptAbi2Extracted.aspis_core.field.QM31
abbrev E := OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact

def putE (out : alloc.vec.Vec U8) (x : E) : Result (alloc.vec.Vec U8) := do
  let a ← WAdm_Fissioned.aspis_core.field.wide_exact.WideExact.to_le_bytes x
  let s ← lift (Array.to_slice a)
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s

def putWord (out : alloc.vec.Vec U8) (x : U32) : Result (alloc.vec.Vec U8) := do
  let a := core.num.U32.to_le_bytes x
  let s ← lift (Array.to_slice a)
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s

def putDigest (out : alloc.vec.Vec U8) (x : Array U8 32#usize) : Result (alloc.vec.Vec U8) := do
  let s ← lift (Array.to_slice x)
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s

theorem put_e (out : alloc.vec.Vec U8) (x : E)
    (bound : out.val.length + 32 ≤ Usize.max) :
    ∃ after, putE out x = ok after ∧ after.val = out.val ++ CheckpointBytesE.rawBytes x := by
  have hb : out.val.length + (CheckpointBytesE.rawBytes x).length ≤ Usize.max := by
    rw [CheckpointBytesE.rawBytes_length]; exact bound
  exact ⟨_,by simpa only [putE,WAdm_Fissioned.aspis_core.field.wide_exact.WideExact.to_le_bytes,
    Array.to_slice,lift,bind_tc_ok] using WAdm_VecStd.extend out ⟨CheckpointBytesE.rawBytes x,by
      rw [CheckpointBytesE.rawBytes_length]; scalar_tac⟩ hb,rfl⟩

theorem put_digest (out : alloc.vec.Vec U8) (x : Array U8 32#usize)
    (bound : out.val.length + 32 ≤ Usize.max) :
    ∃ after, putDigest out x = ok after ∧ after.val = out.val ++ x.val := by
  have hb : out.val.length + x.val.length ≤ Usize.max := by rw [x.property]; exact bound
  exact ⟨_,by simpa only [putDigest,Array.to_slice,lift,bind_tc_ok] using
    WAdm_VecStd.extend out x.to_slice hb,rfl⟩

theorem put_k (out : alloc.vec.Vec U8) (x : K)
    (bound : out.val.length + 16 ≤ Usize.max) :
    ∃ after, WAdm_putK out x = ok after ∧ after.val = out.val ++ CheckpointP6EncodeK.bytes x := by
  obtain ⟨encoded,call,layout⟩ := CheckpointP6EncodeK.encode_k_total x
  have hb : out.val.length + encoded.val.length ≤ Usize.max := by rw [encoded.property]; exact bound
  have eq : WAdm_putK out x = (do
      let encoded ← OraclePortCkptAbi2Extracted.encode_k x
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out encoded.to_slice) := by
    rfl
  rw [eq,call]
  refine ⟨_,?_,?_⟩
  · simpa only [bind_tc_ok] using WAdm_VecStd.extend out encoded.to_slice hb
  · simp only [layout]

#print axioms put_e
#print axioms put_digest
#print axioms put_k
end AspisR1.WAdm_EmittedScalars
end
