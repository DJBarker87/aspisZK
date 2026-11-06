import NKV_TailProgram
import NKV_TailTotal
set_option autoImplicit false
noncomputable section
namespace NKV_TailModel
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1 MultiproofConeRef
open NKV_StepErasure NKV_LoopTransport NKV_ReturnBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
abbrev HashState := AspisV8R19.SourceDuplexStep.State
attribute [local instance] Classical.propDecidable

def observe : Result (ControlFlow NKV_StepErasure.State Out) → Result (Unit × Indices × Values)
 | .ok (.done out) => reject (returned out)
 | .ok (.cont _) => fail .panic
 | .fail e => fail e | .div => div

def model (out : Bool × reference.Scratch) : Result (Unit × Indices × Values) :=
 if out.1 then ok ((),out.2.idx,out.2.val) else fail .panic

theorem verify (out : Bool × reference.Scratch) :
 observe (ok (.done (NKV_TailContinue.returned out)))=model out := by
 rcases out with ⟨keep,s⟩
 cases keep <;> rfl

theorem source (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (root : Array U8 32#usize) (batch : Nat) (kind lo n slot : Usize)
 (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot p kind.val))
 (hb : batch<2) (hk : kind.val<3) (value : slot.val=3*batch+kind.val)
 (keys : Array U64 16#usize) (s : reference.Scratch) (bound : s.n.val≤16) :
 ∃ nodes,(NKV_ConcreteChildren.ops H).op3 proof slot=ok nodes ∧
 observe (NKV_FRef.verifier.candidate.batch_tree_loop.body (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind () lo n slot keys s.idx s.val s.n n)=
 model (eval H (MultiproofConeVerifyState.tailState p batch kind.val nodes s)).2 := by
 obtain ⟨nodes,nodeRead,width,bytes⟩:=NKV_SlotInvocation.physical H proof len p wire batch kind.val hb hk slot value
 refine ⟨nodes,nodeRead,?_⟩
 rw [NKV_TailProgram.source p batch kind.val nodes s width root rootValue]
 by_cases well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s)
 · rw [if_pos well]
   by_cases fits : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)≤OraclePortSelectedDraft.capacity (3*batch+kind.val)
   · obtain ⟨same,read,width2,step⟩:=NKV_TailContinue.source H proof len p wire root batch kind lo n slot hb hk value keys s bound well fits
     have eq : same=nodes := Result.ok.inj (read.symm.trans nodeRead)
     subst same
     rw [step]
     by_cases padded : MultiproofConePadding.scan
         (4*(OraclePortSelectedDraft.capacity (3*batch+kind.val)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))
         ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys s)))=true
     · rw [if_pos padded,if_pos ⟨fits,padded⟩]
       exact verify _
     · rw [if_neg padded,if_neg (by intro h;exact padded h.2)]
       rfl
   · rw [NKV_TailReject.capacity H proof len p wire root batch kind lo n slot hb hk value keys s bound well (by omega)]
     rw [if_neg (by intro h;exact fits h.1)]
     rfl
 · rw [if_neg well,NKV_TailReject.missing H proof root kind lo n slot keys s bound well]
   rfl

set_option pp.proofs false
#print source
#print axioms verify
#print axioms source
end NKV_TailModel
end
