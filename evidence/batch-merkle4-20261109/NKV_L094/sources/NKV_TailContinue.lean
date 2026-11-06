import NKV_TailReject
import NKV_PaddingValue
set_option autoImplicit false
noncomputable section
namespace NKV_TailContinue
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1 MultiproofConeRef
open NKV_StepErasure NKV_LoopTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeSlices MultiproofConeCanonical

def returned (out : Bool × reference.Scratch) : Out :=
 (out.2.idx,out.2.val,(if out.1 then .Ok () else .Err .Merkle),!out.1)

theorem source (H : Bytes → AspisV8R19.SourceDuplexStep.State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=bytesOf proof.val)
 (root : Array U8 32#usize) (batch : Nat) (kind lo n slot : Usize)
 (hb : batch<2) (hk : kind.val<3) (value : slot.val=3*batch+kind.val)
 (keys : Array U64 16#usize) (s : reference.Scratch) (bound : s.n.val≤16)
 (well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s))
 (fits : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)≤
   OraclePortSelectedDraft.capacity (3*batch+kind.val)) :
 ∃ nodes,(NKV_ConcreteChildren.ops H).op3 proof slot=ok nodes ∧
 nodes.val.length=32*OraclePortSelectedDraft.capacity (3*batch+kind.val) ∧
 NKV_FRef.verifier.candidate.batch_tree_loop.body (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind () lo n slot keys s.idx s.val s.n n=
 (if MultiproofConePadding.scan
     (4*(OraclePortSelectedDraft.capacity (3*batch+kind.val)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
     ((bytesOf nodes.val).drop (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s))) then
   ok (.done (returned (eval H (NJV_TX2Returning.endpoint root
     (MultiproofConeSlotTail.prefixNodes nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
       s.idx s.val s.n)).2))
  else ok (.done (s.idx,s.val,.Err .Parse,true))) := by
 obtain ⟨count,countRead,countValue⟩:=NKV_CountInvocation.present s bound well
 obtain ⟨nodes,nodeRead,width,bytes⟩:=NKV_SlotInvocation.physical H proof len p wire batch kind.val hb hk slot value
 obtain ⟨cap,capRead,capValue,small⟩:=NKV_SlotInvocation.capacity slot (by omega)
 have capEq : cap.val=OraclePortSelectedDraft.capacity (3*batch+kind.val) := by rw [capValue,value]
 have countBound : count.val≤172 := by rw [countValue];rw [capEq] at small;omega
 have notexceeds : ¬count>cap := by change ¬cap.val<count.val;rw [countValue,capEq];omega
 have scaled:=NKV_TailArithmetic.scaled_value count countBound
 have fit : (Usize.wrapping_mul 32#usize count).val≤nodes.val.length := by rw [scaled,width,countValue];omega
 let padding:=Slice.drop nodes (Usize.wrapping_mul 32#usize count)
 have paddingRead:=drop_total nodes (Usize.wrapping_mul 32#usize count) fit
 have paddingLength : padding.val.length=8*(4*(OraclePortSelectedDraft.capacity (3*batch+kind.val)-
     OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s))) := by
   simp only [padding,Slice.drop,List.length_drop,scaled,width,countValue]
   omega
 obtain ⟨ce,after,chunksRead,scanRead⟩:=NKV_PaddingValue.source H padding _ paddingLength
 have paddingBytes : bytesOf padding.val=(bytesOf nodes.val).drop
     (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)) := by
   simp only [padding,Slice.drop,bytesOf,List.map_drop,scaled,countValue]
 rw [paddingBytes] at scanRead
 have prefixRead:=prefix_total nodes (Usize.wrapping_mul 32#usize count) fit
 have prefixEq : sub nodes 0#usize (Usize.wrapping_mul 32#usize count)=
     MultiproofConeSlotTail.prefixNodes nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)) := by
   apply Subtype.ext
   simp only [sub,MultiproofConeSlotTail.prefixNodes,List.drop_zero,show (0#usize).val=0 from rfl,
     Nat.sub_zero,scaled,countValue]
 rw [prefixEq] at prefixRead
 refine ⟨nodes,nodeRead,width,?_⟩
 change NJS_Extract.verifier.candidate.slot NGD_SlotRef.slot_offset proof slot=ok nodes at nodeRead
 unfold NKV_FRef.verifier.candidate.batch_tree_loop.body
 rw [if_neg (lt_irrefl n),NKV_CountInvocation.read s bound]
 simp only [bind_tc_ok,NKV_ConcreteChildren.ops]
 rw [countRead]
 simp only [bind_tc_ok,Port3_BatchStd.okOr,core.result.Result.Insts.CoreOpsTry.branch]
 rw [nodeRead]
 simp only [bind_tc_ok,Aeneas.Std.uncurry]
 rw [capRead]
 simp only [bind_tc_ok,Aeneas.Std.uncurry]
 rw [if_neg notexceeds]
 simp only [lift,bind_tc_ok]
 rw [paddingRead]
 simp only [bind_tc_ok,Aeneas.Std.uncurry]
 rw [chunksRead]
 simp only [bind_tc_ok,Aeneas.Std.uncurry]
 simp only [NKV_PaddingInstall.predicate,NKV_ConcreteChildren.ops] at scanRead
 rw [scanRead]
 simp only [bind_tc_ok,Aeneas.Std.uncurry]
 cases guard : MultiproofConePadding.scan
     (4*(OraclePortSelectedDraft.capacity (3*batch+kind.val)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
     ((bytesOf nodes.val).drop (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s))) with
 | false => simp only [guard,Bool.not_false,if_true,Bool.false_eq_true,if_false]
 | true =>
   simp only [guard,Bool.not_true,Bool.false_eq_true,if_false,if_true,lift,bind_tc_ok]
   rw [prefixRead]
   simp only [bind_tc_ok,NKV_ConcreteChildren.verify]
   cases verdict : (eval H (NJV_TX2Returning.endpoint root
     (MultiproofConeSlotTail.prefixNodes nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
       s.idx s.val s.n)).2.1 <;> simp only [verdict,bind_tc_ok,Aeneas.Std.uncurry,returned,if_true,if_false,Bool.not_true,Bool.not_false]

set_option pp.proofs false
#print source
#print axioms source
end NKV_TailContinue
end
