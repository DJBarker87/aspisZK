import NKV_CountInvocation
import NKV_SlotInvocation
set_option autoImplicit false
noncomputable section
namespace NKV_TailReject
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

/-- At the terminal position malformed SAME physical indices return Merkle;
there is no later slot, padding or verifier event. -/
theorem missing (H : Bytes → HashState) (proof : Slice U8) (root : Array U8 32#usize)
 (kind lo n slot : Usize) (keys : Array U64 16#usize) (s : reference.Scratch)
 (bound : s.n.val≤16) (bad : ¬OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s)) :
 NKV_FRef.verifier.candidate.batch_tree_loop.body (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind () lo n slot keys s.idx s.val s.n n=
 ok (.done (s.idx,s.val,.Err .Merkle,true)) := by
 unfold NKV_FRef.verifier.candidate.batch_tree_loop.body
 rw [if_neg (lt_irrefl n),NKV_CountInvocation.read s bound]
 simp only [bind_tc_ok,NKV_ConcreteChildren.ops]
 rw [NKV_CountInvocation.missing s bound bad]
 rfl

/-- Count and fixed slot are derived from CLOSED children on this proof and
scratch, and the actual capacity comparison selects Parse before padding. -/
theorem capacity (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (root : Array U8 32#usize) (batch : Nat) (kind lo n slot : Usize)
 (hb : batch<2) (hk : kind.val<3) (value : slot.val=3*batch+kind.val)
 (keys : Array U64 16#usize) (s : reference.Scratch) (bound : s.n.val≤16)
 (well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s))
 (over : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)>
   OraclePortSelectedDraft.capacity (3*batch+kind.val)) :
 NKV_FRef.verifier.candidate.batch_tree_loop.body (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind () lo n slot keys s.idx s.val s.n n=
 ok (.done (s.idx,s.val,.Err .Parse,true)) := by
 obtain ⟨count,countRead,countValue⟩:=NKV_CountInvocation.present s bound well
 obtain ⟨nodes,nodeRead,width,bytes⟩:=NKV_SlotInvocation.physical H proof len p wire batch kind.val hb hk slot value
 obtain ⟨cap,capRead,capValue,small⟩:=NKV_SlotInvocation.capacity slot (by omega)
 have exceeds : count>cap := by change cap.val<count.val;rw [countValue,capValue,value];exact over
 unfold NKV_FRef.verifier.candidate.batch_tree_loop.body
 rw [if_neg (lt_irrefl n),NKV_CountInvocation.read s bound]
 simp only [bind_tc_ok,NKV_ConcreteChildren.ops]
 rw [countRead]
 simp only [bind_tc_ok,Port3_BatchStd.okOr,core.result.Result.Insts.CoreOpsTry.branch]
 rw [nodeRead]
 simp only [bind_tc_ok]
 rw [capRead,if_pos exceeds]

set_option pp.proofs false
#print missing
#print capacity
#print axioms missing
#print axioms capacity
end NKV_TailReject
end
