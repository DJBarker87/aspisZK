import NNH_MerkleTerminalExecute
import NLL_Invocation
import MultiproofConeLeafFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MerkleLoopExecute
open Aeneas Aeneas.Std NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
attribute [local instance] Classical.propDecidable

def run (H : Bytes → State) (proof : Slice U8) (root : Root)
 (batch : Nat) (kind lo slot : Usize) : Nat → Frame → List Event × Answer
 | 0,f => NNH_MerkleTerminalExecute.run H root batch kind.val (nodeView H proof slot) f.scratch
 | fuel+1,f =>
   if bound : f.scratch.n.val<16 then
    match MultiproofConeLeafContent.next f.scratch
     (Port4B_NativeLeaf.decodedIndex (key f)) (digest H proof kind lo f) bound with
    | none => ([event H proof kind lo f],(.Err .Merkle,f.scratch.idx,f.scratch.val))
    | some next =>
      let tail := run H proof root batch kind lo slot fuel (advance f next)
      (event H proof kind lo f::tail.1,tail.2)
   else ([],(.Err .Parse,f.scratch.idx,f.scratch.val))

theorem native (H : Bytes → State) (proof : Slice U8) (root : Root)
 (batch : Nat) (kind lo n slot : Usize) (small : n.val ≤ 16)
 (fuel : Nat) (f : Frame) (span : f.position.val+fuel=n.val)
 (room : f.scratch.n.val+fuel ≤ 16) :
 Loop H proof root batch kind lo n slot f
  (run H proof root batch kind lo slot fuel f).1
  (run H proof root batch kind lo slot fuel f).2 := by
 induction fuel generalizing f with
 | zero =>
   have done : ¬ f.position<n := by change ¬f.position.val<n.val; omega
   exact .terminal f done _ _ (NNH_MerkleTerminalExecute.native _ _ _ _ _ _)
 | succ fuel ih =>
   have more : f.position<n := by change f.position.val<n.val; omega
   have bound : f.scratch.n.val<16 := by omega
   have source := MultiproofConeLeafContent.step_exact f.scratch
    (Port4B_NativeLeaf.decodedIndex (key f)) (digest H proof kind lo f) bound
   simp only [run,dif_pos bound]
   cases step : MultiproofConeLeafContent.next f.scratch
    (Port4B_NativeLeaf.decodedIndex (key f)) (digest H proof kind lo f) bound with
   | none =>
     rw [step] at source ⊢
     exact .reject f more source
   | some next =>
     rw [step] at source ⊢
     have nextBound := MultiproofConeLeafFold.next_bound f.scratch
      (Port4B_NativeLeaf.decodedIndex (key f)) (digest H proof kind lo f) bound next step
     have position : (advance f next).position.val=f.position.val+1 := by
      exact Port3_Wrapping.increment f.position (by scalar_tac)
     apply Loop.next f next more source _ _
     apply ih (advance f next)
     · rw [position]; omega
     · change next.n.val+fuel ≤ 16; omega
#print axioms native
end AspisR1.NNH_MerkleLoopExecute
