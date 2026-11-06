import NKV_LeafBuild
import NKV_BatchGeometry
set_option autoImplicit false
noncomputable section
namespace NKV_LeafTraversal
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1
open MultiproofConeRef NKV_StepErasure NKV_LoopTransport
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
abbrev HashState := AspisV8R19.SourceDuplexStep.State

def finish (H : Bytes → HashState) (proof : Slice U8) (root : Array U8 32#usize)
 (kind lo n slot : Usize) (keys : Array U64 16#usize) : Result NKV_LeafBuild.Answer → Result Out
 | .fail e => fail e
 | .div => div
 | .ok (false,s) => ok (s.idx,s.val,.Err .Merkle,false)
 | .ok (true,s) => NKV_FRef.verifier.candidate.batch_tree_loop (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind s.idx s.val () lo n slot keys s.n n

/-- Full returning/rejecting/aborting leaf traversal at SAME sorted keys and
original proof. No successful leaf/loop premise. Tail is entered only after
all leaves; a duplicate mismatch retains its exact scratch and stops. -/
theorem source (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
 (q : Fin 22 → Fin 262144) (batch : Nat) (kind lo n slot : Usize)
 (root : Array U8 32#usize) (keys : Array U64 16#usize) (positions : List Nat)
 (s : reference.Scratch) (pos : Usize)
 (members : ∀ selected∈positions,selected∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
 (loValue : lo.val=(if batch=0 then 0 else 10))
 (span : pos.val+positions.length=n.val) (small : n.val≤16)
 (room : s.n.val+positions.length≤16)
 (stream : Port4B_LeafLoop.KeyStream q batch kind.val keys pos positions) :
 NKV_FRef.verifier.candidate.batch_tree_loop (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind s.idx s.val () lo n slot keys s.n pos=
 finish H proof root kind lo n slot keys (NKV_LeafBuild.build H parsed q kind.val positions s).2 := by
 induction positions generalizing s pos with
 | nil =>
   have same : pos=n := UScalar.eq_of_val_eq (by simpa using span)
   subst pos
   rfl
 | cons selected rest ih =>
   have more : pos<n := by change pos.val<n.val;simp only [List.length_cons] at span;omega
   have bound : s.n.val<16 := by simp only [List.length_cons] at room;omega
   have keyRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed q batch kind.val selected) :=
     stream pos 0 (by simp) (by omega)
   obtain ⟨view,viewRead,width,address,reads,body⟩:=NKV_LeafInvocation.source H proof len parsed wire
     q batch selected kind lo n slot pos root keys s (members selected (by simp))
     loValue more bound keyRead []
   conv_lhs => unfold NKV_FRef.verifier.candidate.batch_tree_loop
   rw [Aeneas.Std.loop.eq_def]
   simp only [Aeneas.Std.uncurry,body]
   cases reply : reference.leaf_step s (MultiproofConeLeafFold.key q kind.val selected)
       (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected))) with
   | fail e => simp only [reply,bind_tc_ok,bind_tc_fail,bind_tc_div,NKV_LeafBuild.build,finish]
   | div => simp only [reply,bind_tc_ok,bind_tc_fail,bind_tc_div,NKV_LeafBuild.build,finish]
   | ok out =>
     cases out with
     | none => simp only [reply,bind_tc_ok,NKV_LeafStep.project,NKV_LeafBuild.build,finish]
     | some t =>
       have next := reply
       rw [MultiproofConeLeafContent.step_exact s _ _ bound] at next
       have choice:=Result.ok.inj next
       have count:=MultiproofConeLeafFold.next_bound s _ _ bound t choice
       have advance:=Port3_Wrapping.increment pos (by omega)
       have following : Port4B_LeafLoop.KeyStream q batch kind.val keys
           (Usize.wrapping_add pos 1#usize) rest := by
         intro cursor j hj value
         have read:=stream cursor (j+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hj)
           (by rw [advance] at value;omega)
         simpa only [List.getElem_cons_succ] using read
       have tail:=ih t (Usize.wrapping_add pos 1#usize)
         (fun p hp => members p (List.mem_cons_of_mem _ hp))
         (by rw [advance];simp only [List.length_cons] at span;omega)
         (by simp only [List.length_cons] at room;omega) following
       simp only [reply,bind_tc_ok,NKV_LeafStep.project,NKV_LeafBuild.build]
       exact tail

set_option pp.proofs false
#print source
#print axioms source
end NKV_LeafTraversal
end
