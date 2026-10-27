import RPu_FIx_PathLoop
import RPu_FIx_ArrayMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PathLiteral
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings

def initial (selector bit : NQ) : Fin (17#usize).val → K :=
  Function.update (fun _=>0) ⟨0,by decide⟩ (decode selector*(decode bit*(decode bit-1)))

theorem value (selector : NQ) (o : Openings) (out : Array NQ 17#usize)
    (hs : Canon selector) (hz : canonical o.z) (hsucc : canonical o.succ_z)
    (success : pool_v1.pair_forest_semantic_terminal.path_lanes_literal selector o=ok out) :
    ∃ bit,Array.index_usize o.z 0#usize=ok bit ∧ Canon bit ∧ canonical out ∧
      decoded out=FIx_PathLoop.model selector bit o.z o.succ_z 8 0 (initial selector bit) := by
  unfold pool_v1.pair_forest_semantic_terminal.path_lanes_literal at success
  obtain ⟨bit,hbit,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q,hq,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,hq1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q2,hq2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨a,ha,success⟩ := FIv_Map.bind_success _ _ _ success
  have hb := FIv_NativeArray.canonical o.z 0#usize bit hz hbit
  have vq := FIv_SubMap.qm bit field.QM31.ONE q hb FIv_NativeValue.one.1 hq
  have vq1 := FIv_NativeValue.mul bit q q1 hb vq.1 hq1
  have vq2 := FIv_NativeValue.mul selector q1 q2 hs vq1.1 hq2
  have zero : canonical (Array.repeat 17#usize field.QM31.ZERO) := by
    intro x hx
    have same : x=field.QM31.ZERO := List.eq_of_mem_replicate hx
    rw [same]
    exact FIv_NativeValue.zero.1
  have update := FIw_ArrayValue.update _ a 0#usize q2 (by decide) zero vq2.1 ha
  have loop := FIx_PathLoop.value 8 ⟨0#usize,poseidon2.DIGEST_ELEMS⟩ selector bit o.z o.succ_z a out
    (by rw [poseidon2.DIGEST_ELEMS];rfl) (by rfl) hs hb hz hsucc update.1 success
  refine ⟨bit,hbit,hb,loop.1,?_⟩
  rw [loop.2,update.2,FIx_ArrayMeaning.decoded_repeat,vq2.2,vq1.2,vq.2,FIv_NativeValue.one.2,FIv_NativeValue.zero.2]
  rfl
#print axioms value
end AspisR1.FIx_PathLiteral
end
