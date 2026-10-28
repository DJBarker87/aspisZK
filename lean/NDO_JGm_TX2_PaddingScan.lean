import JGm_TX2_AnyFalse
import NDO_JGk_TX2_Padding0
import NDO_JGk_TX2_Padding1
import NDO_JGk_TX2_Padding2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_PaddingScan
open Aeneas Aeneas.Std Result

theorem chunk_replicate (n : Nat) :
    (List.toChunksExact 8 (by decide) (List.replicate (8*n) 0#u8)).1=
      List.replicate n (List.replicate 8 0#u8) := by
  induction n with
  | zero => simp [List.toChunksExact]
  | succ n ih =>
    rw [List.toChunksExact]
    simp only [List.length_replicate,Nat.mul_succ,Nat.not_lt.mpr (by omega : 8≤8*n+8),dif_neg]
    simp only [List.take_replicate,List.drop_replicate,Nat.min_eq_left (by omega : 8≤8*n+8),Nat.add_sub_cancel]
    simp only [ih,_root_.dite_false,List.replicate_succ]
#print axioms chunk_replicate

theorem predicate {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (chunk : Slice U8) (bytes : chunk.val=List.replicate 8 0#u8) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool.call_mut
      (Port3_BatchStd.install Port4B_Install.leaves) D () chunk=ok (false,()) := by
  have same : chunk=JGm_TX2_AnyFalse.zero := Subtype.ext bytes
  rw [same]
  exact JGm_TX2_AnyFalse.predicate D
#print axioms predicate

theorem source {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X)
    (padding : Slice U8) (bytes : padding.val=List.replicate 288 0#u8)
    (ce : core.slice.iter.ChunksExact U8)
    (chunks : core.slice.Slice.chunks_exact padding 8#usize=ok ce) :
    (Port3_BatchStd.install Port4B_Install.leaves).op0
      (core.iter.traits.iterator.IteratorChunksExact U8)
      (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
        (Port3_BatchStd.install Port4B_Install.leaves) D) ce ()=
        ok (false,{chunks:=[],remainder:=ce.remainder}) := by
  apply JGm_TX2_AnyFalse.source
  intro chunk mem
  unfold core.slice.Slice.chunks_exact at chunks
  split at chunks
  next positive =>
    cases Result.ok.inj chunks
    obtain ⟨c,_,eq⟩ := List.mem_map.mp mem
    rcases c with ⟨c,hc⟩
    have member : c∈(List.toChunksExact 8 (by decide) padding.val).1 := hc
    rw [bytes,show 288=8*36 from rfl,chunk_replicate] at member
    have cb := List.eq_of_mem_replicate member
    apply predicate D
    simpa only [←eq] using cb
  next bad => simp at bad
#print axioms source
end AspisR1.JGm_TX2_PaddingScan
end
