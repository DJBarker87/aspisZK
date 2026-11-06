import NLK_LaneProgram
import NLK_LaneTrace
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_LaneInvocation
open Aeneas Aeneas.Std Result AspisR1 NKP_LaneCuts
abbrev Lane := NLA_LaneAssemble.Lane
abbrev PE := NKF_BoxModel.PE
attribute [local instance] Classical.propDecidable
/-- Full source-ordered native-cut schema, with ONE immutable original input.
The branches are the literal return sites: bad extent, prefix, root, loop,
then the terminal/actual-owned-carrier suffix. Trace is per-occurrence native
cuts, NOT a whole loop equation or a second independent execution. The native
association of every clause is recorded separately; this definition itself
is not native evidence and earns no row credit. -/
def Cut (bytes : Slice U8) (allocated : Nat)
 (out : core.result.Result (NKY_BoxAction.Owned Lane) PE) : Prop :=
 if h : bytes.val.length=768 then
  let p : NLK_LaneInput.Sized := ⟨bytes,h⟩
  match NLK_LaneHeader.sourcePrefix p with
  | .Err e => out=.Err e
  | .Ok f =>
   match NLK_LaneDigest.decode (NLK_LaneInput.root p) with
   | .Err _ => out=.Err .InvalidAccountData
   | .Ok root => ∃ loop : Reply × Frontier × List (Fin 20),
      NLK_LaneTrace.Cut p f.next NLK_LaneLoop.levels NLK_LaneLoop.zero loop ∧
      match loop.1 with
      | .Err e => out=.Err e
      | .Ok _ => NLK_LaneSuffixLaw.Cut f.bump f.master f.lane f.next root
          NLK_LaneTable.final loop.2.1 allocated out
 else out=.Err .InvalidAccountData

theorem log_irrelevant (bump : U8) (master : Array U8 32#usize) (lane : U8)
 (next : U64) (root empty : Node) (reply : Reply) (state : Frontier)
 (first second : List (Fin 20)) :
 (NKP_LaneCompletion.finish bump master lane next root empty (reply,state,first)).1 =
 (NKP_LaneCompletion.finish bump master lane next root empty (reply,state,second)).1 := by
 cases reply with
 | Err e => rfl
 | Ok u =>
   by_cases bad : next.val=0 ∧ root≠empty
   · simp only [NKP_LaneCompletion.finish,if_pos bad]
   · simp only [NKP_LaneCompletion.finish,if_neg bad]

/-- All Result arms and every returned window reconstruct the single wire
reference. Only the explicitly reviewed parent-cut schema is a hypothesis;
no Ops, successful child, allocator success or desired output equation occurs. -/
theorem value (bytes : Slice U8) (allocated : Nat)
 (out : core.result.Result (NKY_BoxAction.Owned Lane) PE) (cut : Cut bytes allocated out) :
 ok (NKY_BoxCarrier.erase out)=NLK_LaneProgram.reference bytes := by
 rw [NLK_LaneProgram.source]
 unfold Cut at cut
 unfold NLK_LaneProgram.referenceValue
 by_cases h : bytes.val.length=768
 · simp only [dif_pos h] at cut ⊢
   let p : NLK_LaneInput.Sized := ⟨bytes,h⟩
   change ok (NKY_BoxCarrier.erase out)=ok (NLK_LaneProgram.body p)
   change (match NLK_LaneHeader.sourcePrefix p with
    | .Err e => out=.Err e
    | .Ok f => match NLK_LaneDigest.decode (NLK_LaneInput.root p) with
      | .Err _ => out=.Err .InvalidAccountData
      | .Ok root => ∃ loop, NLK_LaneTrace.Cut p f.next NLK_LaneLoop.levels NLK_LaneLoop.zero loop ∧
        match loop.1 with
        | .Err e => out=.Err e
        | .Ok _ => NLK_LaneSuffixLaw.Cut f.bump f.master f.lane f.next root
            NLK_LaneTable.final loop.2.1 allocated out) at cut
   unfold NLK_LaneProgram.body
   cases parsed : NLK_LaneHeader.sourcePrefix p with
   | Err e => simp only [parsed] at cut ⊢;rw [cut];rfl
   | Ok f =>
    simp only [parsed] at cut ⊢
    cases rootReply : NLK_LaneDigest.decode (NLK_LaneInput.root p) with
    | Err e => simp only [rootReply] at cut ⊢;rw [cut];rfl
    | Ok root =>
     simp only [rootReply] at cut ⊢
     obtain ⟨loop,trace,last⟩ := cut
     have same := NLK_LaneTrace.source p f.next NLK_LaneLoop.levels NLK_LaneLoop.zero loop trace
     rw [←same]
     rcases loop with ⟨reply,state,calls⟩
     cases reply with
     | Err e => rw [last];rfl
     | Ok u =>
      have suffix := NLK_LaneSuffixLaw.value f.bump f.master f.lane f.next root
       NLK_LaneTable.final state allocated out last
      rw [log_irrelevant f.bump f.master f.lane f.next root NLK_LaneTable.final (.Ok u) state calls []]
      cases u
      exact congrArg Result.ok suffix
 · simp only [dif_neg h] at cut ⊢
   rw [cut];rfl

theorem owner (bytes : Slice U8) (allocated : Nat)
 (out : core.result.Result (NKY_BoxAction.Owned Lane) PE) (cut : Cut bytes allocated out) :
 NKY_BoxCarrier.Owner allocated out := by
 unfold Cut at cut
 split at cut
 · dsimp only at cut
   split at cut
   · rw [cut];trivial
   · split at cut
     · rw [cut];trivial
     · obtain ⟨loop,trace,last⟩:=cut
       rcases loop with ⟨reply,state,calls⟩
       cases reply with
       | Err e => rw [last];trivial
       | Ok u =>
        cases out with
        | Err e => trivial
        | Ok box => exact last.2.2
 · rw [cut];trivial

theorem owned {S : Type} (allocator : S2W_D189Wrappers.Allocator S)
 (before : S) (reservation : NP6_StdModel.Reservation)
 (bytes : Slice U8) (allocated : Nat)
 (out : core.result.Result (NKY_BoxAction.Owned Lane) PE) (cut : Cut bytes allocated out) :
 NKY_BoxCarrier.native allocator before 720 reservation out =
 NLK_LaneProgram.owned allocator before reservation allocated bytes := by
 rw [NKY_BoxCarrier.association allocator before 720 reservation allocated out (owner bytes allocated out cut)]
 unfold NLK_LaneProgram.owned
 rw [value bytes allocated out cut]

#print value
#print axioms value
#print owner
#print axioms owner
#print owned
#print axioms owned
#print axioms log_irrelevant
end NLK_LaneInvocation
