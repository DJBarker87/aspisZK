import Port10AUTH_TerminalCut
import Port4B_SliceReads
import Port4B_Capacity

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Tail
open Aeneas Aeneas.Std Result ControlFlow
open MultiproofConeRef
open Port3_NativeBatchCalls (Indices Values)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical MultiproofConeSlices MultiproofConePhysicalViews MultiproofConeSlotTail
attribute [local instance] Classical.propDecidable

/-- Full accepted emitted terminal observation transport. Count, width and padding come
from that SAME accepted iteration; the native verifier supplies its own
source success. Only input provenance, successful-read interpretation and local parent lowerings remain. -/
theorem accepted (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (occupied sibling : MultiproofConeP6Callbacks.Parent)
    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (b : Nat) (kind lo n slot : Usize) (hb : b<2) (hk : kind.val<3) (slotValue : slot.val=3*b+kind.val)
    (root : Array U8 32#usize) (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot parsed kind.val))
    (keys : Array U64 16#usize) (s : reference.Scratch) (outIdx : Indices) (outVal : Values)
    (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port9OR_BatchStep.ops base) D proof root kind hash lo n slot
      keys s.idx s.val s.n n=ok (.done (outIdx,outVal,some (.Ok ())))) :
    ∃ nodes final,
      Port4B_SlotInstall.nodeSlot proof slot=ok nodes ∧
      bytesOf nodes.val=OraclePortCompactDraft.slice parsed.wire (OraclePortSelectedDraft.slotStart (3*b+kind.val))
        (32*OraclePortSelectedDraft.capacity (3*b+kind.val)) ∧
      eval H (MultiproofConeP6Batch.tailState (MultiproofConeP6Callbacks.nodeWith occupied sibling)
        parsed b kind.val nodes s)=
        (CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys s.idx s.val s.n n)).1,(true,final)) ∧ final.idx=outIdx ∧ final.val=outVal := by
  obtain ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,capRead,
    fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead,terminalLogs⟩ :=
    Port10AUTH_TerminalCut.accepted base D hash proof root kind lo n slot keys s outIdx outVal run
  have frontEq := Port4B_SliceReads.live_indices s front frontRead
  have counted := Port4B_CountInstall.accepted_count front count countRead
  rw [frontEq] at counted
  have countValue : count.val=slotCount s := counted.2.1.trans (slot_count_eq s).symm
  have capValue := Port4B_Capacity.read slot cap b kind.val hb hk slotValue capRead
  have countBound : count.val≤cap.val := by exact Nat.le_of_not_gt fit
  obtain ⟨view,viewRead,width,bytes⟩ := Port4B_SlotInstall.physical proof len parsed wire b kind.val hb hk slot slotValue
  have sameNodes : view=nodes := Result.ok.inj (viewRead.symm.trans nodeRead)
  subst view
  have widthCap : nodes.val.length=32*cap.val := width.trans (congrArg (32*·) capValue).symm
  have scale := Port4B_SliceReads.scaled count counted.2.2
  have scaleFit : (Usize.wrapping_mul 32#usize count).val≤nodes.val.length := by rw [scale,widthCap];omega
  have padRead := drop_total nodes (Usize.wrapping_mul 32#usize count) scaleFit
  have samePadding := Result.ok.inj (paddingRead.symm.trans padRead)
  have padContent : padding.val=nodes.val.drop (32*count.val) := by
    simpa only [Slice.drop,scale] using congrArg (fun x : Slice U8 => x.val) samePadding
  have padLength : padding.val.length=32*(cap.val-count.val) := by rw [padContent,List.length_drop,widthCap];omega
  have zeroBytes := Port4B_Padding.native_zero (Port4B_VerifyInstall.install base) D padding
    (by rw [padLength];omega) ce after chunksRead scanRead
  have allZero : (bytesOf padding.val).all (fun byte => byte==0)=true := by
    apply List.all_eq_true.mpr
    intro byte mem
    change byte∈padding.val.map decodeByte at mem
    obtain ⟨raw,rawMem,rfl⟩ := List.mem_map.mp mem
    have same := zeroBytes raw rawMem
    subst raw
    rfl
  have padScan : MultiproofConePadding.scan (4*(cap.val-count.val)) (bytesOf padding.val)=true := by
    rw [MultiproofConePadding.scan_all _ _ (by simp only [bytesOf,List.length_map,padLength];omega)]
    exact allZero
  have prefixChecked := prefix_total nodes (Usize.wrapping_mul 32#usize count) scaleFit
  have sameSupplied := Result.ok.inj (prefixRead.symm.trans prefixChecked)
  have suppliedEq : supplied=prefixNodes nodes count.val := by
    apply Subtype.ext
    simpa only [sub,List.drop_zero,show (0#usize).val=0 from rfl,Nat.sub_zero,scale,prefixNodes]
      using congrArg (fun x : Slice U8 => x.val) sameSupplied
  have suppliedLength : supplied.val.length=32*count.val := by
    rw [suppliedEq]
    simp only [prefixNodes,List.length_take]
    apply Nat.min_eq_left
    rw [widthCap];omega
  change (do let (accepted,out) ← MultiproofConeRef.reference.verify_owned (Port4B_VerifyInstall.digest D) hash
      root {s with «at»:=0#usize} supplied; ok (accepted,out.idx,out.val))=ok (true,outIdx,outVal) at verifyRead
  obtain ⟨⟨accepted,final⟩,nativeVerify,output⟩ := Port3_PushFrame.bind_success _ _ _ verifyRead
  have same := Result.ok.inj output
  simp only [Prod.mk.injEq] at same
  obtain ⟨truth,indices,values⟩ := same
  subst accepted
  have codeSuccess := (Port9OR_P6Verify.source D hash root s supplied).trans nativeVerify
  have verified := Port10AUTH_Verify.accepted D hash H oracle
    (MultiproofConeP6Callbacks.nodeWith occupied sibling)
    (MultiproofConeP6Callbacks.node_gate (rawOracle H) occupied sibling occupiedGate siblingGate)
    root s final supplied counted.1 (by rw [suppliedLength];omega)
    (by rw [suppliedLength];have c:=MultiproofConeP6Frozen2Stage.capacity_bound b kind.val hb hk;omega) codeSuccess
  have projectedLogs : (Port9OR_Code.trace D hash (Port9OR_BatchStep.verify root s.idx s.val s.n supplied)).1=
      (Port9OR_Code.trace D hash (Port9OR_P6Verify.code root s supplied)).1 :=
    Port10AUTH_TerminalCut.map_log D hash _ (fun out => (out.1,out.2.idx,out.2.val))
  rw [← projectedLogs,← terminalLogs] at verified
  have padBytes : bytesOf padding.val=(bytesOf nodes.val).drop (32*count.val) := by
    simp only [bytesOf,padContent,List.map_drop]
  have checks : slotCount s≤OraclePortSelectedDraft.capacity (3*b+kind.val) ∧
      (bytesOf nodes.val).length=32*OraclePortSelectedDraft.capacity (3*b+kind.val) ∧
      MultiproofConePadding.scan (4*(OraclePortSelectedDraft.capacity (3*b+kind.val)-slotCount s))
        ((bytesOf nodes.val).drop (32*slotCount s))=true := by
    refine ⟨?_,?_,?_⟩
    · rw [←countValue,←capValue];exact countBound
    · simpa only [bytesOf,List.length_map] using width
    · rw [←countValue,←capValue,←padBytes];exact padScan
  refine ⟨nodes,final,nodeRead,bytes,?_,indices,values⟩
  rw [suppliedEq,countValue,rootValue] at verified
  simpa only [MultiproofConeP6Batch.tailState,if_pos counted.1,if_pos checks] using verified

#print axioms accepted
end AspisR1.Port10AUTH_Tail
end
