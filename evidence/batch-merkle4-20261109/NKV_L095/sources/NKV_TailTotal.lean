import NKV_TailContinue
set_option autoImplicit false
noncomputable section
namespace NKV_TailTotal
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1 MultiproofConeRef
open NKV_StepErasure NKV_LoopTransport
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem body (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (root : Array U8 32#usize) (batch : Nat) (kind lo n slot : Usize)
 (hb : batch<2) (hk : kind.val<3) (value : slot.val=3*batch+kind.val)
 (keys : Array U64 16#usize) (s : reference.Scratch) (bound : s.n.val≤16) :
 ∃ out,NKV_FRef.verifier.candidate.batch_tree_loop.body (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind () lo n slot keys s.idx s.val s.n n=ok (.done out) := by
 by_cases well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s)
 · by_cases fits : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)≤
       OraclePortSelectedDraft.capacity (3*batch+kind.val)
   · obtain ⟨nodes,read,width,step⟩:=NKV_TailContinue.source H proof len p wire root batch kind lo n slot hb hk value keys s bound well fits
     split at step <;> exact ⟨_,step⟩
   · exact ⟨_,NKV_TailReject.capacity H proof len p wire root batch kind lo n slot hb hk value keys s bound well (by omega)⟩
 · exact ⟨_,NKV_TailReject.missing H proof root kind lo n slot keys s bound well⟩

theorem loop (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (root : Array U8 32#usize) (batch : Nat) (kind lo n slot : Usize)
 (hb : batch<2) (hk : kind.val<3) (value : slot.val=3*batch+kind.val)
 (keys : Array U64 16#usize) (s : reference.Scratch) (bound : s.n.val≤16) :
 ∃ out,NKV_FRef.verifier.candidate.batch_tree_loop (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind s.idx s.val () lo n slot keys s.n n=ok out := by
 obtain ⟨out,step⟩:=body H proof len p wire root batch kind lo n slot hb hk value keys s bound
 refine ⟨out,?_⟩
 unfold NKV_FRef.verifier.candidate.batch_tree_loop
 rw [Aeneas.Std.loop.eq_def]
 simp only [Aeneas.Std.uncurry,step]

set_option pp.proofs false
#print body
#print loop
#print axioms body
#print axioms loop
end NKV_TailTotal
end
