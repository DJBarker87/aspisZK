import F3Q_TailView
import F3Q_TerminalLog
import F3Q_VerifyAccepted
import F3Q_VerifyCall
import Port4B_SliceReads
import Port4B_Capacity

set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_TailFacts
open Aeneas Aeneas.Std Result ControlFlow
open MultiproofConeRef
open Port3_NativeBatchCalls (Indices Values)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical MultiproofConeSlices MultiproofConePhysicalViews MultiproofConeSlotTail
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MultiproofConeP6Verify.verifyState MultiproofConeP6Composition.levels

/-- Full accepted native terminal transport. Count, width and padding come
from that SAME accepted iteration; the native verifier supplies its own
source success. Only input provenance and the named P6Boundary remain. -/
theorem accepted {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (Port4B_VerifyInstall.digest D) hash H binary occupied sibling leaf)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (b : Nat) (kind lo n slot : Usize) (hb : b<2) (hk : kind.val<3) (slotValue : slot.val=3*b+kind.val)
    (root : Array U8 32#usize) (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot parsed kind.val))
    (keys : Array U64 16#usize) (s : reference.Scratch) (outIdx : Indices) (outVal : Values)
    (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install (Port4B_VerifyInstall.install Port4B_Install.leaves)) D proof root kind hash lo n slot
      keys s.idx s.val s.n n=ok (.done (outIdx,outVal,some (.Ok ())))) :
    ∃ nodes supplied,
      Port4B_SlotInstall.nodeSlot proof slot=ok nodes ∧
      bytesOf nodes.val=OraclePortCompactDraft.slice parsed.wire (OraclePortSelectedDraft.slotStart (3*b+kind.val))
        (32*OraclePortSelectedDraft.capacity (3*b+kind.val)) ∧
      supplied=prefixNodes nodes (slotCount s) ∧
      OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst) ∧
      (slotCount s≤OraclePortSelectedDraft.capacity (3*b+kind.val) ∧
        (bytesOf nodes.val).length=32*OraclePortSelectedDraft.capacity (3*b+kind.val) ∧
        MultiproofConePadding.scan (4*(OraclePortSelectedDraft.capacity (3*b+kind.val)-slotCount s))
          ((bytesOf nodes.val).drop (32*slotCount s))=true) ∧
      supplied.val.length%32=0 ∧ supplied.val.length≤5504 ∧
      Port4B_Install.leaves.op10 D hash Port3_NativeBatchBody.multiproof.Arity.Two root s.idx s.val s.n supplied=
        ok (true,outIdx,outVal) ∧
      (eval H (SdkC_Oracle.program (Port9OR_BatchStep.body Port4B_Install.leaves D proof root kind hash
        lo n slot keys s.idx s.val s.n n))).1=
        (eval H (SdkC_Oracle.program (Port9OR_P6Verify.code root {s with «at»:=0#usize} supplied))).1 := by
  obtain ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,capRead,
    fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead⟩ :=
    Port4B_TailReads.reads (Port4B_VerifyInstall.install Port4B_Install.leaves) D hash proof root kind lo n slot s.n
      keys s.idx outIdx s.val outVal run
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
  have zeroBytes := Port4B_Padding.native_zero (Port4B_VerifyInstall.install Port4B_Install.leaves) D padding
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
  have terminalLog := F3Q_TerminalLog.of_reads D hash H p6.oracle proof root kind lo n slot s.n
    keys s.idx outIdx s.val outVal front count cap nodes padding supplied ce after
    frontRead countRead nodeRead capRead fit paddingRead chunksRead scanRead prefixRead verifyRead
  refine ⟨nodes,supplied,nodeRead,bytes,?_,counted.1,checks,?_,?_,verifyRead,terminalLog⟩
  · rw [suppliedEq,countValue]
  · rw [suppliedLength];omega
  · rw [suppliedLength]
    have c:=MultiproofConeP6Frozen2Stage.capacity_bound b kind.val hb hk
    omega

#print axioms accepted
end AspisR1.F3Q_TailFacts
end
