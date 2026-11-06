import NKV_TailModel
set_option autoImplicit false
noncomputable section
namespace NKV_TailLoop
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef
open NKV_StepErasure NKV_LoopTransport NKV_ReturnBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem source (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (root : Array U8 32#usize) (batch : Nat) (kind lo n slot : Usize)
 (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot p kind.val))
 (hb : batch<2) (hk : kind.val<3) (value : slot.val=3*batch+kind.val)
 (keys : Array U64 16#usize) (s : reference.Scratch) (bound : s.n.val≤16) :
 ∃ nodes,(NKV_ConcreteChildren.ops H).op3 proof slot=ok nodes ∧
 reject (NKV_FRef.verifier.candidate.batch_tree_loop (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind s.idx s.val () lo n slot keys s.n n >>= returned)=
 NKV_TailModel.model (eval H (MultiproofConeVerifyState.tailState p batch kind.val nodes s)).2 := by
 obtain ⟨nodes,read,model⟩:=NKV_TailModel.source H proof len p wire root batch kind lo n slot rootValue hb hk value keys s bound
 obtain ⟨out,step⟩:=NKV_TailTotal.body H proof len p wire root batch kind lo n slot hb hk value keys s bound
 rw [step] at model
 refine ⟨nodes,read,?_⟩
 unfold NKV_FRef.verifier.candidate.batch_tree_loop
 rw [Aeneas.Std.loop.eq_def]
 simp only [Aeneas.Std.uncurry,step,bind_tc_ok]
 exact model

set_option pp.proofs false
#print source
#print axioms source
end NKV_TailLoop
end
