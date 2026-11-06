import NLL_State
set_option autoImplicit false
noncomputable section
namespace NLL_TerminalStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1 MultiproofConeRef
open NLL NKV_StepErasure NKV_LoopTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Intermediate terminal step, not a row root: the surrounding leaf fold
must supply the actual node view and verifier byte domain. Every constructor
uses the complete child Result and BOTH returned arrays. -/
theorem value (H : Bytes → State) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (root : NLL.Root) (batch : Nat) (kind lo n slot : Usize)
 (hb : batch<2) (hk : kind.val<3) (value : slot.val=3*batch+kind.val)
 (keys : NLL.Keys) (s : reference.Scratch) (bound : s.n.val≤16)
 (nodes : Slice U8) (nodeRead : (NKV_ConcreteChildren.ops H).op3 proof slot=ok nodes)
 (bytes : (MultiproofConeSlotTail.prefixNodes nodes (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s))).val.length≤9216)
 (events : List Event) (out : NLL.Answer) (native : Terminal H root batch kind.val nodes s events out) :
 (NKV_FRef.verifier.candidate.batch_tree_loop (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind s.idx s.val () lo n slot keys s.n n >>=
     NKV_ReturnBoundary.returned)=ok out := by
 have body : NKV_FRef.verifier.candidate.batch_tree_loop.body (NKV_ConcreteChildren.ops H)
     (NKV_ConcreteChildren.digest H) proof root kind () lo n slot keys s.idx s.val s.n n >>=
     (fun cf => match cf with | .done x => NKV_ReturnBoundary.returned x | .cont _ => fail .panic)=ok out := by
   cases native with
   | missing bad => rw [NKV_TailReject.missing H proof root kind lo n slot keys s bound bad];rfl
   | capacity well excess =>
     rw [NKV_TailReject.capacity H proof len p wire root batch kind lo n slot hb hk value keys s bound well excess];rfl
   | padding well fits bad =>
     obtain ⟨same,read,width,step⟩:=NKV_TailContinue.source H proof len p wire root batch kind lo n slot hb hk value keys s bound well fits
     have eq : same=nodes := Result.ok.inj (read.symm.trans nodeRead)
     subst same
     rw [step,bad];rfl
   | verify well fits pad queries answer child =>
     obtain ⟨same,read,width,step⟩:=NKV_TailContinue.source H proof len p wire root batch kind lo n slot hb hk value keys s bound well fits
     have eq : same=nodes := Result.ok.inj (read.symm.trans nodeRead)
     subst same
     have packet:=NKV_VerifyInvocation.returning H root _ s.idx s.val s.n bytes queries answer child
     have result:=congrArg Prod.snd packet
     change ok ((eval H (NJV_TX2Returning.endpoint root _ s.idx s.val s.n)).2.1,
       (eval H (NJV_TX2Returning.endpoint root _ s.idx s.val s.n)).2.2.idx,
       (eval H (NJV_TX2Returning.endpoint root _ s.idx s.val s.n)).2.2.val)=ok _ at result
     have result':=Result.ok.inj result
     rw [step,pad]
     simp only [if_true,bind_tc_ok,NKV_TailContinue.returned,NKV_ReturnBoundary.returned]
     exact congrArg (fun a : Bool × NLL.Indices × NLL.Values =>
       ok ((if a.1 then .Ok () else .Err .Merkle),a.2.1,a.2.2)) result'
 obtain ⟨answer,step⟩:=NKV_TailTotal.body H proof len p wire root batch kind lo n slot hb hk value keys s bound
 rw [step] at body
 unfold NKV_FRef.verifier.candidate.batch_tree_loop
 rw [Aeneas.Std.loop.eq_def]
 simpa only [Aeneas.Std.uncurry,step,bind_tc_ok] using body

set_option pp.proofs false
#print value
#print axioms value
end NLL_TerminalStep
end
