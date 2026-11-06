import NLL_Invocation
set_option autoImplicit false
noncomputable section
namespace NLL_LoopDomains
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Every verifier occurrence in the SAME native invocation has the live
count inherited from its actual preceding iterations. This bound does not
assume a successful whole tree, accepted verifier, or chosen scratch. -/
theorem source (H : Bytes → State) (proof : Slice U8) (root : NLL.Root) (batch : Nat)
 (kind lo n slot : Usize) (f : Frame) (events : List Event) (out : NLL.Answer)
 (native : Loop H proof root batch kind lo n slot f events out)
 (smallN : n.val≤16) (limit : Nat) (cap : limit≤16) (pos : f.position.val≤n.val)
 (invariant : f.scratch.n.val+(n.val-f.position.val)≤limit)
 (nodes : Slice U8) (count : Nat) (before : reference.Scratch)
 (queries : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (answer : Bool × NJP_RowModel.Scratch)
 (entered : Event.verify nodes count before queries answer∈events) :
 before.n.val≤limit ∧ OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys before) := by
 induction native with
 | reject f more step => simp only [List.mem_singleton,event] at entered;cases entered
 | next f t more step events out tail ih =>
   have small : f.scratch.n.val<16 := by change f.position.val<n.val at more;omega
   have exactStep:=step
   rw [MultiproofConeLeafContent.step_exact f.scratch _ _ small] at exactStep
   have countBound:=MultiproofConeLeafFold.next_bound f.scratch _ _ small t (Result.ok.inj exactStep)
   have inc:=Port3_Wrapping.increment f.position (by change f.position.val<n.val at more;omega)
   have remaining : Event.verify nodes count before queries answer∈events := by
     simp only [List.mem_cons,event] at entered
     rcases entered with bad|good
     · cases bad
     · exact good
   apply ih (by change (Usize.wrapping_add f.position 1#usize).val≤n.val;rw [inc];change f.position.val<n.val at more;omega)
     (by change t.n.val+(n.val-(Usize.wrapping_add f.position 1#usize).val)≤limit;rw [inc];change f.position.val<n.val at more;omega) remaining
 | terminal f done events out terminal =>
   have bound : f.scratch.n.val≤limit := by omega
   cases terminal with
   | missing bad => simp only [List.mem_singleton] at entered;cases entered
   | capacity well excess => simp only [List.mem_singleton] at entered;cases entered
   | padding well fits bad => simp only [List.mem_singleton] at entered;cases entered
   | verify well fits pad qs ans child =>
     simp only [List.mem_singleton] at entered
     injection entered with nodesEq countEq beforeEq queriesEq answerEq
     cases beforeEq
     exact ⟨bound,well⟩

set_option pp.proofs false
#print source
#print axioms source
end NLL_LoopDomains
end
