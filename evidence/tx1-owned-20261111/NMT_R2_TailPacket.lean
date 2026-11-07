import NMT_R2_ResultTry
import NMT_345TailFold
set_option autoImplicit false
noncomputable section
namespace NMT_R2_TailPacket
open Aeneas Aeneas.Std NMT_345

structure Point (W : Type) extends Bounds W where
 public_ : Public
 proofView : Slice U8
 k : Usize

def tail {W : Type} (c : Calls) (s : Bounds W) : Result (core.result.Result (Point W) PE) := do
 if Slice.len s.proofData != s.proofEnd then NMT_R2_ResultTry.throw .InvalidAccountData else do
  let proofPrefix ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   s.proofData {«end» := s.proofStart}
  let mismatch ← c.c0 core.cmp.PartialEqU8 proofPrefix s.candidate
  if mismatch then NMT_R2_ResultTry.throw .InvalidAccountData else do
   let offset ← lift (Usize.wrapping_add s.proofStart 8#usize)
   let tag ← Slice.index_usize s.proofData offset
   let expected ← c.c3 NMT_stage1_owned.aspis_r1_cost_probe.transport.Variant.S2
   if tag != expected then NMT_R2_ResultTry.throw .InvalidAccountData else do
    let pub ← c.c5 s.statement
    let proof ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
     s.proofData {start := s.proofStart,«end» := s.proofEnd}
    let kbyte ← Slice.index_usize s.data 1#usize
    let k ← lift (UScalar.cast .Usize kbyte)
    NMT_R2_ResultTry.pure ⟨s,pub,proof,k⟩

def finish {W : Type} (c : Calls) (s : Point W) : Result Ret :=
 NMT_R2_ResultTry.bind (c.c11 s.public_ s.publicData s.proofView s.k) fun checkpoint =>
 if alloc.vec.Vec.len checkpoint != Slice.len s.checkpointData
 then .ok (.Err .InvalidAccountData) else .ok (.Ok checkpoint)

/-- Exact source tail, factored at the sole eventful child occurrence. -/
theorem source {W : Type} (c : Calls) (s : Bounds W) :
 NMT_R2_ResultTry.bind (tail c s) (finish c) = tailFold c s := by
 simp only [tail,Bind.bind,NMT_R2_ResultTry.outer,NMT_R2_ResultTry.choose,
  NMT_R2_ResultTry.throw_left,NMT_R2_ResultTry.pure_left]
 rfl
#print axioms source
end NMT_R2_TailPacket
end
