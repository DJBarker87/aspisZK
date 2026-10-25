import T2Nat_ReaderBody
import T2Nat_ScalarStage
import T2Nat_RawStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2Nat_TailFactor
open Aeneas Aeneas.Std Result AspisR1Stage2
open T2Nat_ResultEq

def tail (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let different ← ops.ne core.cmp.PartialEqU8 checksum digest
  if different then ok (.Err .Checkpoint) else
    let (state,r1) ← ops.raw 32#usize ⟨bytes,80#usize⟩
    let (root0,r2) ← ops.raw 32#usize r1
    let (root1,r3) ← ops.raw 32#usize r2
    T2Nat_ScalarStage.body ops bytes v next finish state root0 root1 r3

theorem source_eq (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    tail ops bytes v next finish checksum digest = T2Nat_ReaderBody.tail ops bytes v next finish checksum digest := rfl

theorem congr (reserved : Bool) (bytes : Slice U8) (v : transport.Variant)
    (next : U8) (finish : Usize) (checksum : Slice U8) (digest : Array U8 32#usize) :
    EqOk (tail (T2Nat_ReaderOps.ops reserved) bytes v next finish checksum digest)
      (tail (CheckpointBytes4Ops.ops reserved) bytes v next finish checksum digest) := by
  change EqOk
    (T2Nat_RawStage.body (T2Nat_ReaderOps.ops reserved).raw
      ((T2Nat_ReaderOps.ops reserved).ne core.cmp.PartialEqU8 checksum digest)
      (T2Nat_ScalarStage.body (T2Nat_ReaderOps.ops reserved) bytes v next finish) ⟨bytes,80#usize⟩)
    (T2Nat_RawStage.body (CheckpointBytes4Ops.ops reserved).raw
      ((CheckpointBytes4Ops.ops reserved).ne core.cmp.PartialEqU8 checksum digest)
      (T2Nat_ScalarStage.body (CheckpointBytes4Ops.ops reserved) bytes v next finish) ⟨bytes,80#usize⟩)
  exact T2Nat_RawStage.congr _ _ (T2Nat_ReaderOps.raw reserved) _ _ _
    (T2Nat_ScalarStage.congr reserved bytes v next finish) _

#print axioms source_eq
#print axioms congr
end AspisR1.T2Nat_TailFactor
end
