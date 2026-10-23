import Port3_BatchStd

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_BatchStage
open Aeneas Aeneas.Std Result
open Port3_NativeBatchCalls (Indices Values)

abbrev Prepared := VTop_Stages.verifier.Prepared
abbrev Digest := Array U8 32#usize

def root0 (p : Prepared) : Digest := p.roots.val[0]'(by simp [p.roots.property])
def root1 (p : Prepared) : Digest := p.roots.val[1]'(by simp [p.roots.property])
def roots (p : Prepared) (folded : Digest) : Array Digest 3#usize := Array.make 3#usize [root0 p,root1 p,folded]

def batch (leaves : Port3_NativeBatchBody.Ops) {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (proof : Slice U8) (p : Prepared) (folded : Digest) (which : Usize) (hash : H) :=
  Port3_QueryInstall.result (Port3_NativeBatchBody.verifier.candidate.batch_merkle
    (Port3_BatchStd.install leaves) (VTop_Checkpoint.digest D) proof p folded which hash)

def installed (base : VTop_Stages.Ops) (reserved : Bool)
    (aops : AspisR1Stage2.AccumulateOps) (qops : AspisR1Stage2.QueryOps)
    (leaves : Port3_NativeBatchBody.Ops) : VTop_Stages.Ops :=
  {Port3_NativePendingInstall.installed base reserved aops qops with op5 := batch leaves}

/-- Same physical Prepared queries, two stored roots and actual folded-root
argument. No parsed/model root or independent batch witness is substituted. -/
theorem parent_success (leaves : Port3_NativeBatchBody.Ops) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H) (proof : Slice U8) (p : Prepared)
    (folded : Digest) (which : Usize) (hash : H)
    (accepted : batch leaves D proof p folded which hash=ok (.Ok ())) :
    Port3_NativeBatchBody.verifier.candidate.batch_merkle_values (Port3_BatchStd.install leaves)
      (VTop_Checkpoint.digest D) proof p.queries (roots p folded) which hash=ok (.Ok ()) := by
  have native := (Port3_QueryInstall.success_iff _ _).mp accepted
  have h0 : Array.index_usize p.roots 0#usize=ok (root0 p) := by
    simp [Array.index_usize,root0]
  have h1 : Array.index_usize p.roots 1#usize=ok (root1 p) := by
    simp [Array.index_usize,root1]
  unfold Port3_NativeBatchBody.verifier.candidate.batch_merkle at native
  simpa only [h0,h1,bind_tc_ok,roots] using native

theorem accepted_slot_calls (leaves : Port3_NativeBatchBody.Ops) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H) (proof : Slice U8) (p : Prepared)
    (folded : Digest) (which : Usize) (hash : H)
    (accepted : batch leaves D proof p folded which hash=ok (.Ok ())) :
    ∃ (idx1 idx2 idx3 : Indices) (val1 val2 val3 : Values),
      Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install leaves)
        (VTop_Checkpoint.digest D) proof p.queries (root0 p) which 0#usize
        (Array.repeat 16#usize 0#u32) (Array.repeat 16#usize (Array.repeat 32#usize 0#u8)) hash =
        ok (.Ok (),idx1,val1) ∧
      Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install leaves)
        (VTop_Checkpoint.digest D) proof p.queries (root1 p) which 1#usize idx1 val1 hash =
        ok (.Ok (),idx2,val2) ∧
      Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install leaves)
        (VTop_Checkpoint.digest D) proof p.queries folded which 2#usize idx2 val2 hash =
        ok (.Ok (),idx3,val3) := by
  have calls := Port3_NativeBatchCalls.values_calls (Port3_BatchStd.install leaves)
    (VTop_Checkpoint.digest D) hash proof p.queries (roots p folded) which
    (parent_success leaves D proof p folded which hash accepted)
  simpa [Port3_NativeBatchCalls.rootAt,roots,Array.make] using calls

#print axioms parent_success
#print axioms accepted_slot_calls
end AspisR1.Port3_BatchStage
end
