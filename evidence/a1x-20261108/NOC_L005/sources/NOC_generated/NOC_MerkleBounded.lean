import NNY_MerkleShared
import NNX_LeafAgreement
import LIBC_HashShapes
import LIBC_BatchMerkle
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_MerkleBounded
/-! Restatement of the read-only NNY_MerkleShared chain (rows .. parent) under the
bounded leaf companion. Proof bodies are copied unchanged; only the agreement
structure differs. NNY sources are not edited. -/
open AspisR1.NNY_MerkleShared (refDigest totalDigest total endpoint_total slotBound)
section agreement
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Bounded companion of NNY_MerkleShared.NodeLeaf. Node shapes are as in
the shared interface; the leaf law is required only on the reached 832-byte
openings (NNX_PARTITION_FINDING: the unrestricted leaf law is false for
LIBC_CohortHash.H on short openings). -/
structure NodeLeaf (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → State) : Prop where
 node : ∀ left right : Array U8 32#usize,
  D.digest () (MultiproofConePhysicalDigest.parts left right) =
   ok (MultiproofConePhysicalTransport.rawOracle H (MultiproofConePhysicalDigest.parts left right))
 leaf : ∀ (kind : Usize) (opening : Slice U8), opening.val.length=832 →
  D.digest () (Port4B_LeafCode.input kind opening) =
   ok (MultiproofConePhysicalTransport.rawOracle H (Port4B_LeafCode.input kind opening))
theorem node (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (s : MultiproofConeRef.reference.Scratch)
 (physical : Slice U8) (i w : Usize) :
 MultiproofConeRef.reference.binary_step (refDigest D) () s physical i w =
 MultiproofConeRef.reference.binary_step (totalDigest D H) () s physical i w := by
 have left := NNU_MerkleNode.node (refDigest D) ()
  (MultiproofConePhysicalTransport.rawOracle H) agree.node s physical i w
 have right := NNU_MerkleNode.node (totalDigest D H) ()
  (MultiproofConePhysicalTransport.rawOracle H) (fun _ _ => rfl) s physical i w
 exact left.symm.trans right
theorem leaf (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (kind : Usize) (opening : Slice U8)
 (len : opening.val.length=832) :
 Port4B_LeafCode.native (VTop_Checkpoint.digest D) () kind opening =
 ok (MultiproofConePhysicalTransport.rawOracle H (Port4B_LeafCode.input kind opening)) := by
 rw [Port4B_LeafCode.native,(Port4B_LeafCode.code_exact _ () kind opening len []).1]
 exact agree.leaf kind opening len
end agreement
section rows
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
/-- Source recursion follows total auxiliary progress, but uses only node-shape agreement. -/
theorem rows (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (physical : Slice U8) (fuel : Nat)
 (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w)
 (bound : s.n.val-i.val ≤ fuel) :
 reference.level_rows (refDigest D) () s physical i w =
 reference.level_rows (totalDigest D H) () s physical i w := by
 induction fuel generalizing s i w with
 | zero =>
   have halt : i≥s.n := by obtain ⟨_,_,_,_,_⟩ := domain; scalar_tac
   rw [reference.level_rows,reference.level_rows]
   simp only [halt,if_true]
 | succ fuel ih =>
   rw [reference.level_rows,reference.level_rows]
   by_cases halt : i≥s.n
   · simp only [halt,if_true]
   · simp only [halt,if_false,node D H agree]
     obtain ⟨out,eqout,post⟩ := binary_step_progress (totalDigest D H) () (total D H)
      physical s i w domain (by scalar_tac)
     rw [eqout]
     simp only [bind_tc_ok]
     cases out with
     | Stop stopped => rfl
     | Next next ni nw =>
       obtain ⟨sameN,nextDomain,advance,_⟩ := post
       exact ih next ni nw nextDomain (by rw [sameN];omega)
theorem level (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (physical : Slice U8) (s : reference.Scratch)
 (domain : Domain physical s) :
 reference.level_rows (refDigest D) () s physical 0#usize 0#usize =
 reference.level_rows (totalDigest D H) () s physical 0#usize 0#usize :=
 rows D H agree physical s.n.val s _ _ ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩ (by simp)
end rows
section height
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
theorem iterate (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (physical : Slice U8) (height : Nat) (s : reference.Scratch)
 (domain : Domain physical s) :
 MultiproofConeLevelIteration.iterate
  (fun s => reference.level_rows (refDigest D) () s physical 0#usize 0#usize) height s =
 MultiproofConeLevelIteration.iterate
  (fun s => reference.level_rows (totalDigest D H) () s physical 0#usize 0#usize) height s :=
 NNY_HeightCongruence.iterate _ _ (Domain physical)
  (fun s hs => level D H agree physical s hs)
  (fun s t hs run => level_preserve (totalDigest D H) () (total D H) physical s t hs run)
  height s domain

theorem height (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → State)
 (agree : NodeLeaf D H) (physical : Slice U8) (s : reference.Scratch)
 (domain : Domain physical s) :
 reference.levels (refDigest D) () s physical 18#u32 =
 reference.levels (totalDigest D H) () s physical 18#u32 := by
 rw [levels_eq_iteration _ () physical 18#u32 (by decide) s,
  levels_eq_iteration _ () physical 18#u32 (by decide) s]
 exact iterate D H agree physical 18 s domain
end height
section endpoint
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalViews MultiproofConePhysicalTransport
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

theorem endpoint (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
 (agree : NodeLeaf D H) (root : Array U8 32#usize) (physical : Slice U8)
 (s out : reference.Scratch) (zero : s.«at»=0#usize)
 (accepted : (eval H (MultiproofConeVerifyState.verifyState root physical s)).2=(true,out)) :
 reference.verify_owned (refDigest D) () root s physical=.ok (true,out) := by
 have native := endpoint_total D H root physical s out zero accepted
 have guard : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst) ∧ physical.val.length%32=0 := by
  by_contra bad
  simp only [MultiproofConeVerifyState.verifyState,if_neg bad,eval] at accepted
  cases accepted
 obtain ⟨positive,bound,indices⟩ := NNU_MerkleHead.source s guard.1
 have domain : MultiproofConeLevelIteration.Domain physical s := ⟨positive,bound,by rw [zero];simp⟩
 have reset : {s with «at»:=0#usize}=s := by cases s; simp_all only
 have success := Port4B_VerifyInstall.wrapper_success
  (fun s => reference.levels (totalDigest D H) () s physical 18#u32) root s out physical native
 apply NNU_MerkleWrapper.returned (refDigest D) () root s out physical positive bound indices guard.2
 · rw [reset,height D H agree physical s domain]
   rw [reset] at success
   exact success.1
 · exact success.2
end endpoint
section verify
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw

theorem verify (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H) (root : Array U8 32#usize)
 (idx outIdx : Array U32 16#usize) (val outVal : Array (Array U8 32#usize) 16#usize)
 (n : Usize) (physical : Slice U8)
 (accepted : NKV_ConcreteChildren.verify H
  (NKV_ConcreteChildren.digest H) () .Two root idx val n physical=
  .ok (true,outIdx,outVal)) :
 Port4B_VerifyInstall.verify (VTop_Checkpoint.digest D) ()
  .Two root idx val n physical=.ok (true,outIdx,outVal) := by
 let s := NJV_EntryABI.initial idx val n
 let out := (eval H (NJV_TX2Returning.endpoint root physical idx val n)).2
 change Result.ok (out.1,out.2.idx,out.2.val)=Result.ok (true,outIdx,outVal) at accepted
 have values := Result.ok.inj accepted
 have boolean : out.1=true := congrArg Prod.fst values
 have indices : out.2.idx=outIdx := congrArg (fun x => x.2.1) values
 have digests : out.2.val=outVal := congrArg (fun x => x.2.2) values
 have returned : (eval H
   (MultiproofConeVerifyState.verifyState root physical s)).2=(true,out.2) :=
   Prod.ext boolean rfl
 have native := endpoint D H agree root physical s out.2 rfl returned
 unfold Port4B_VerifyInstall.verify
 change (do let (b,after) ← reference.verify_owned (refDigest D) () root s physical
            .ok (b,after.idx,after.val))=.ok (true,outIdx,outVal)
 rw [native]
 simp only [bind_tc_ok,indices,digests]
end verify
section terminal
open Aeneas Aeneas.Std Result MultiproofConeRef
open NKV_StepErasure NKV_LoopTransport

theorem terminal (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H) (proof : Slice U8) (root : Array U8 32#usize)
 (tree lo n slot d : Usize) (keys : Array U64 16#usize)
 (idx outIdx : Indices) (val outVal : Values) (slotBound : slot.val < 6)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H))
  (NKV_ConcreteChildren.digest H) proof root tree () lo n slot keys idx val d n=
  .ok (.done (outIdx,outVal,some (.Ok ())))) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install Port4B_Install.leaves)
  (VTop_Checkpoint.digest D) proof root tree () lo n slot keys idx val d n=
  .ok (.done (outIdx,outVal,some (.Ok ()))) := by
 obtain ⟨front,count,cap,nodes,padding,supplied,ce,after,frontRead,countRead,nodeRead,
   capRead,fit,paddingRead,chunksRead,scanRead,prefixRead,verifyRead⟩ :=
   Port4B_TailReads.reads (NKV_ConcreteChildren.ops H)
    (NKV_ConcreteChildren.digest H) () proof root tree lo n slot d
    keys idx outIdx val outVal run
 have targetCount : Port4B_Install.leaves.op11 .Two front=.ok (some count) := by
   change Port4B_CountInstall.nodeCount .Two front=.ok (some count)
   rw [←NNU_MerkleCount.source]
   exact countRead
 have targetNode : Port4B_Install.leaves.op3 proof slot=.ok nodes := by
   change Port4B_SlotInstall.nodeSlot proof slot=.ok nodes
   rw [←NNU_MerkleChildren.slot proof slot slotBound]
   exact nodeRead
 have targetVerify : Port4B_Install.leaves.op10 (VTop_Checkpoint.digest D) ()
   .Two root idx val d supplied=.ok (true,outIdx,outVal) :=
   verify D H agree root idx outIdx val outVal d supplied verifyRead
 have callback := NNY_MerkleTerminalFrame.callback
   (NKV_ConcreteChildren.ops H) Port4B_Install.leaves
   (NKV_ConcreteChildren.digest H)
   (VTop_Checkpoint.digest D)
 rw [callback] at scanRead
 rw [NNY_MerkleTerminalFrame.source Port4B_Install.leaves _ proof root () tree lo n slot d n keys idx val (by simp)]
 exact NNY_MerkleTerminalBuild.constructed Port4B_Install.leaves _ proof root slot d idx outIdx val outVal
  front count cap nodes padding supplied ce after frontRead targetCount targetNode capRead fit
  paddingRead chunksRead scanRead prefixRead targetVerify
end terminal
section active
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport
/-- One arbitrary active native iteration. The checked opening proves the
leaf domain; the post-hash mutation is literally shared. No scratch invariant
or whole-loop equality is assumed. -/
theorem active (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (agree : NodeLeaf D H) (proof : Slice U8) (root : Array U8 32#usize)
 (tree lo n slot d pos : Usize) (keys : Array U64 16#usize)
 (idx : Indices) (val : Values) (more : pos < n) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H)) (NKV_ConcreteChildren.digest H)
  proof root tree () lo n slot keys idx val d pos =
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  (Port3_BatchStd.install Port4B_Install.leaves) (VTop_Checkpoint.digest D)
  proof root tree () lo n slot keys idx val d pos := by
 rw [Port4B_NativeLeaf.active _ _ () proof root tree lo n slot d pos keys idx val more,
  Port4B_NativeLeaf.active _ _ () proof root tree lo n slot d pos keys idx val more]
 cases keyRead : Array.index_usize keys pos with
 | fail e => simp only [keyRead,bind_tc_fail]
 | div => simp only [keyRead,bind_tc_div]
 | ok key =>
   simp only [keyRead,bind_tc_ok]
   have opening : (NKV_ConcreteChildren.ops H).op2 proof (Port4B_NativeLeaf.openingIndex lo key)=
    Port4B_Install.leaves.op2 proof (Port4B_NativeLeaf.openingIndex lo key) :=
    NNU_MerkleChildren.opening proof _
   rw [opening]
   cases viewRead : Port4B_Install.leaves.op2 proof (Port4B_NativeLeaf.openingIndex lo key) with
   | fail e => simp only [viewRead,bind_tc_fail]
   | div => simp only [viewRead,bind_tc_div]
   | ok view =>
     simp only [viewRead,bind_tc_ok]
     have width := NNY_OpeningWidth.source proof view _ viewRead
     have left := NKV_ConcreteDomains.leaf H (NKV_ConcreteChildren.digest H) () tree view width
     have leftValue : (NKV_ConcreteChildren.ops H).op6 (NKV_ConcreteChildren.digest H) () tree view =
      ok (MultiproofConePhysicalTransport.rawOracle H (Port4B_LeafCode.input tree view)) := by
       rw [left,Port4B_LeafCode.native,(Port4B_LeafCode.code_exact _ () tree view width []).1]
       rfl
     have right := leaf D H agree tree view width
     change (do let l ← (NKV_ConcreteChildren.ops H).op6 (NKV_ConcreteChildren.digest H) () tree view
                Port4B_LeafStep.post idx val d (Port4B_NativeLeaf.decodedIndex key) l (Usize.wrapping_add pos 1#usize)) =
      (do let l ← Port4B_LeafCode.native (VTop_Checkpoint.digest D) () tree view
          Port4B_LeafStep.post idx val d (Port4B_NativeLeaf.decodedIndex key) l (Usize.wrapping_add pos 1#usize))
     rw [leftValue,right]
end active
section loop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport
/-- Accepted-loop transport uses the single native iteration on arbitrary
scratch. Its invariant is True: checked opening reads establish width locally,
and the unchanged post-hash mutation preserves all continued source states. -/
theorem loop (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (agree : NodeLeaf D H) (proof : Slice U8) (root : Array U8 32#usize)
 (tree lo n slot d pos : Usize) (keys : Array U64 16#usize)
 (idx outIdx : Indices) (val outVal : Values) (slotBound : slot.val<6)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H)) (NKV_ConcreteChildren.digest H)
  proof root tree idx val () lo n slot keys d pos = ok (outIdx,outVal,some (.Ok ()))) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
  (Port3_BatchStd.install Port4B_Install.leaves) (VTop_Checkpoint.digest D)
  proof root tree idx val () lo n slot keys d pos = ok (outIdx,outVal,some (.Ok ())) := by
 unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop at run ⊢
 refine NNY_LoopTransport.accepted _ _ (fun out : CohortOut => out.2.2=some (.Ok ()))
  ?_ (idx,val,d,pos) (outIdx,outVal,some (.Ok ())) rfl run
 rintro ⟨i,v,count,cursor⟩ result read
 by_cases more : cursor<n
 · have same := active D H agree proof root tree lo n slot count cursor keys i v more
   cases result <;> simp only <;> (try intro)
   all_goals exact same.symm.trans read
 · have src := NNY_MerkleTerminalFrame.source (NKV_ConcreteChildren.ops H)
    (NKV_ConcreteChildren.digest H) proof root () tree lo n slot count cursor keys i v more
   cases result with
   | cont next =>
     exact False.elim (NNY_TerminalControl.no_cont _ _ proof root slot count i v next (src.symm.trans read))
   | done output =>
     rcases output with ⟨oi,ov,pending⟩
     intro good
     change pending=some (.Ok ()) at good
     subst pending
     have atEnd : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install (NKV_ConcreteChildren.ops H)) (NKV_ConcreteChildren.digest H)
      proof root tree () lo n slot keys i v count n=ok (.done (oi,ov,some (.Ok ()))) := by
       rw [NNY_MerkleTerminalFrame.source _ _ proof root () tree lo n slot count n keys i v (by simp)]
       exact src.symm.trans read
     have target := terminal D H agree proof root tree lo n slot count keys i oi v ov slotBound atEnd
     have dst := NNY_MerkleTerminalFrame.source Port4B_Install.leaves
      (VTop_Checkpoint.digest D) proof root () tree lo n slot count cursor keys i v more
     have dstEnd := NNY_MerkleTerminalFrame.source Port4B_Install.leaves
      (VTop_Checkpoint.digest D) proof root () tree lo n slot count n keys i v (by simp)
     exact dst.trans (dstEnd.symm.trans target)
end loop
section trees
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport Port3_NativeBatchCalls

theorem treeCode (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (tree lo n slot : Usize) (idx outIdx : NKV_StepErasure.Indices) (val outVal : NKV_StepErasure.Values)
 (span : (lo=0#usize ∧ n=10#usize) ∨ (lo=10#usize ∧ n=12#usize))
 (treeBound : tree.val<3) (slotBound : slot.val<6)
 (canonical : ∀ j,j<22 → queries.val[j]!.val<262144)
 (run : NNY_MerkleTreeFrame.code (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
  proof queries root tree lo n slot idx val=ok (.Ok (),outIdx,outVal)) :
 NNY_MerkleTreeFrame.code Port4B_Install.leaves (VTop_Checkpoint.digest D)
  proof queries root tree lo n slot idx val=ok (.Ok (),outIdx,outVal) := by
 unfold NNY_MerkleTreeFrame.code at run ⊢
 obtain ⟨raw,keyRead,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨keys,sortRead,run⟩ := Port3_PushFrame.bind_success _ _ _ run
 have targetKey : Port4B_Install.leaves.op4 queries lo n tree=ok raw := by
  change Port4B_KeyInstall.build queries lo n tree=ok raw
  rw [←NJS_Keys.source queries lo n tree span treeBound canonical]
  exact keyRead
 have lower : 1≤n.val := by rcases span with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
 have upper : n.val≤16 := by rcases span with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
 have targetSort : Port4B_Install.leaves.op5 raw n=ok keys := by
  change MultiproofSortRef.sort_reference.sort_rows raw 1#usize n=ok keys
  rw [←NJS_Sort.source raw n lower upper]
  exact sortRead
 obtain ⟨⟨oi,ov,pending⟩,loopRun,final⟩ := Port3_PushFrame.bind_success _ _ _ run
 cases pending with
 | none => cases final
 | some reply =>
   cases reply with
   | Err e => cases final
   | Ok u =>
     cases u
     have values := Result.ok.inj final
     have ie := congrArg (fun t => t.2.1) values
     have ve := congrArg (fun t => t.2.2) values
     dsimp only at ie ve
     subst outIdx; subst outVal
     have targetLoop := loop D H agree proof root tree lo n slot 0#usize 0#usize
      keys idx oi val ov slotBound loopRun
     rw [targetKey]
     simp only [bind_tc_ok]
     rw [targetSort]
     simp only [bind_tc_ok]
     rw [targetLoop]
     rfl

theorem tree (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H)
 (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
 (k kind : Usize) (hk : k.val<2) (tk : kind.val<3)
 (idx outIdx : NKV_StepErasure.Indices) (val outVal : NKV_StepErasure.Values)
 (canonical : ∀ j,j<22 → queries.val[j]!.val<262144)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H)
  (NKV_ConcreteChildren.digest H) proof queries root k kind idx val ()=ok (.Ok (),outIdx,outVal)) :
 Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install Port4B_Install.leaves)
  (VTop_Checkpoint.digest D) proof queries root k kind idx val ()=ok (.Ok (),outIdx,outVal) := by
 change Port3_NativeBatchBody.verifier.candidate.batch_tree
  (Port3_BatchStd.install (NKV_ConcreteChildren.ops H)) _ _ _ _ _ _ _ _ _ = _ at run
 by_cases zero : k=0#usize
 · subst k
   rw [NNY_MerkleTreeFrame.zero] at run ⊢
   exact treeCode D H agree proof queries root kind 0#usize 10#usize _ idx outIdx val outVal
    (Or.inl ⟨rfl,rfl⟩) tk (slotBound kind 0#usize tk (by decide)) canonical run
 · have one : k=1#usize := UScalar.eq_of_val_eq (by
    have nz : k.val≠0 := by intro h;exact zero (UScalar.eq_of_val_eq h)
    change k.val=1
    omega)
   subst k
   rw [NNY_MerkleTreeFrame.one] at run ⊢
   exact treeCode D H agree proof queries root kind 10#usize 12#usize _ idx outIdx val outVal
    (Or.inr ⟨rfl,rfl⟩) tk (slotBound kind 3#usize tk (by decide)) canonical run
end trees
section shared
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NKV_StepErasure NKV_LoopTransport Port3_NativeBatchCalls

theorem values (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
 (H : Bytes → AspisV8R19.SourceDuplexStep.State) (agree : NodeLeaf D H)
 (proof : Slice U8) (queries : Array U32 22#usize) (roots : Array (Array U8 32#usize) 3#usize)
 (k : Usize) (hk : k.val<2) (canonical : ∀ j,j<22 → queries.val[j]!.val<262144)
 (run : Port3_NativeBatchBody.verifier.candidate.batch_merkle_values (NKV_ConcreteChildren.ops H)
  (NKV_ConcreteChildren.digest H) proof queries roots k ()=ok (.Ok ())) :
 Port3_NativeBatchBody.verifier.candidate.batch_merkle_values (Port3_BatchStd.install Port4B_Install.leaves)
  (VTop_Checkpoint.digest D) proof queries roots k ()=ok (.Ok ()) := by
 obtain ⟨i1,i2,i3,v1,v2,v3,c0,c1,c2⟩ := values_calls _ _ () proof queries roots k run
 have t0 := tree D H agree proof queries (rootAt roots 0) k 0#usize hk (by decide) _ i1 _ v1 canonical c0
 have t1 := tree D H agree proof queries (rootAt roots 1) k 1#usize hk (by decide) i1 i2 v1 v2 canonical c1
 have t2 := tree D H agree proof queries (rootAt roots 2) k 2#usize hk (by decide) i2 i3 v2 v3 canonical c2
 unfold Port3_NativeBatchBody.verifier.candidate.batch_merkle_values
 have h0 : Array.index_usize roots 0#usize=ok (Port3_NativeBatchCalls.rootAt roots 0) := Port3_NativeBatchCalls.root_read roots 0
 have h1 : Array.index_usize roots 1#usize=ok (Port3_NativeBatchCalls.rootAt roots 1) := Port3_NativeBatchCalls.root_read roots 1
 have h2 : Array.index_usize roots 2#usize=ok (Port3_NativeBatchCalls.rootAt roots 2) := Port3_NativeBatchCalls.root_read roots 2
 rw [h0,bind_tc_ok,h1,bind_tc_ok,h2,bind_tc_ok]
 rw [t0]
 simp only [bind_tc_ok, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch]
 rw [t1]
 simp only [bind_tc_ok, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch]
 rw [t2]
 rfl

/-- Lane-neutral parent. Agreement is discharged per lane; it is never an A1/A2 premise. -/
theorem parent (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (agree : NodeLeaf D H)
 (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
 (k : Usize) (hk : k.val<2) (q : ∀ j,j<22 → p.queries.val[j]!.val<262144)
 (accepted : NHT_ResultPort.action (NKV_FRef.verifier.candidate.batch_merkle
  (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof p folded k ())=ok (.Ok ())) :
 Port4B_Install.batch D proof p folded k ()=ok (.Ok ()) := by
 have native := (NKV_OkTransport.batch H proof p folded k hk).mpr (NHT_ResultSuccess.source _ () accepted)
 unfold Port3_NativeBatchBody.verifier.candidate.batch_merkle at native
 obtain ⟨r0,read0,native⟩ := Port3_PushFrame.bind_success _ _ _ native
 obtain ⟨r1,read1,native⟩ := Port3_PushFrame.bind_success _ _ _ native
 have result := values D H agree proof p.queries (Array.make 3#usize [r0,r1,folded]) k hk q native
 unfold Port4B_Install.batch Port3_BatchStage.batch
 apply (Port3_QueryInstall.success_iff _ _).mpr
 unfold Port3_NativeBatchBody.verifier.candidate.batch_merkle
 rw [read0,bind_tc_ok,read1,bind_tc_ok]
 exact result
end shared
section hostInstance
open Aeneas Aeneas.Std Result NNH_Run5bCtx
/-- Node agreement of the literal host checkpoint digest with LIBC's cohort
oracle: binary-node requests are in the LIBC partition shape. -/
theorem hostNode {W Tx : Type} (c : Ctx W Tx) (left right : Array U8 32#usize) :
 (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)).digest ()
  (MultiproofConePhysicalDigest.parts left right) =
 .ok (MultiproofConePhysicalTransport.rawOracle (LIBC_CohortHash.H (envOf c))
  (MultiproofConePhysicalDigest.parts left right)) := by
 rw [NNV_CheckpointDigest.source]
 unfold MultiproofConePhysicalTransport.rawOracle
 rw [LIBC_CohortHash.output (envOf c) _ (LIBC_HashShapes.node left right)]
 rfl
/-- The bounded companion at the host digest and LIBC_CohortHash.H. -/
theorem host {W Tx : Type} (c : Ctx W Tx) :
 NodeLeaf (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)) (LIBC_CohortHash.H (envOf c)) :=
 ⟨hostNode c, fun kind opening len => NNX_LeafAgreement.source c kind opening len⟩
/-- Bounded parent at the host digest and LIBC's oracle. -/
theorem hostParent {W Tx : Type} (c : Ctx W Tx) (proof : Slice U8)
 (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
 (k : Usize) (hk : k.val<2) (q : ∀ j,j<22 → p.queries.val[j]!.val<262144)
 (accepted : NHT_ResultPort.action (NKV_FRef.verifier.candidate.batch_merkle
  (NKV_ConcreteChildren.ops (LIBC_CohortHash.H (envOf c)))
  (NKV_ConcreteChildren.digest (LIBC_CohortHash.H (envOf c))) proof p folded k ())=ok (.Ok ())) :
 Port4B_Install.batch (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)) proof p folded k ()=ok (.Ok ()) :=
 parent _ _ (host c) proof p folded k hk q accepted
/-- Exact k = 0 instance on LIBC's batch model (LIBC_BatchMerkle.source is
the NKV link; Domain supplies k = 0 and the canonical queries). -/
theorem model0 {W Tx : Type} (c : Ctx W Tx) (a : LIBC_BatchMerkle.Args)
 (domain : LIBC_BatchMerkle.Domain a)
 (accepted : NHT_ResultPort.action (LIBC_BatchMerkle.model a (envOf c))=ok (.Ok ())) :
 Port4B_Install.batch (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)) (LIBC_Bytes.raw a.1)
  (LIBC_BatchMerkle.prepared a) (LIBC_BatchMerkle.folded a) 0#usize ()=ok (.Ok ()) := by
 have zero : LIBC_Usize.raw a.2.2.2=0#usize := by
  rw [domain.1];exact LIBC_Usize.from_native 0#usize (by scalar_tac)
 rw [LIBC_BatchMerkle.source,zero] at accepted
 exact hostParent c _ _ _ 0#usize (by decide) domain.2.2.1 accepted
end hostInstance
#print axioms node
#print axioms leaf
#print axioms rows
#print axioms level
#print axioms iterate
#print axioms height
#print axioms endpoint
#print axioms verify
#print axioms terminal
#print axioms active
#print axioms loop
#print axioms treeCode
#print axioms tree
#print axioms values
#print axioms parent
#print axioms hostNode
#print axioms host
#print axioms hostParent
#print axioms model0
end AspisR1.NOC_MerkleBounded
end
