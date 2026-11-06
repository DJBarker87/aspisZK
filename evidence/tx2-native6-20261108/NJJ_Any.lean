import NIL_HeaderAny
set_option autoImplicit false
noncomputable section
namespace NJJ_Any
open Aeneas Aeneas.Std Result AspisR1
/-- Hand library model of Iterator::any with the resume byte predicate.
The state is the complete pinned Aeneas iterator, not a Bool-only summary.
One loop step is NJJ_lib::any_step; docs and source pins in NJJ_LIBMODELS.md. -/
def run : Nat → core.slice.iter.Iter U8 → Result (Bool × core.slice.iter.Iter U8)
 | 0,it => ok (false,it)
 | n+1,it => do
   let (value,rest) ← core.slice.iter.IteratorSliceIter.next it
   match value with
   | none => ok (false,rest)
   | some b => if b != 0#u8 then ok (true,rest) else run n rest

theorem loop (n : Nat) (it : core.slice.iter.Iter U8) :
 run n it=CheckpointBytes4Ops.headerLoop n it := by
 induction n generalizing it with
 | zero => rfl
 | succ n ih =>
   unfold run CheckpointBytes4Ops.headerLoop
   cases h : core.slice.iter.IteratorSliceIter.next it with
   | fail err => rfl
   | div => rfl
   | ok x =>
     rcases x with ⟨value,rest⟩
     cases value with
     | none => rfl
     | some b =>
       simp only [bind_tc_ok]
       change (if b != 0#u8 then ok (true,rest) else run n rest)=
        (if b != 0#u8 then ok (true,rest) else CheckpointBytes4Ops.headerLoop n rest)
       rw [ih]

def any (it : core.slice.iter.Iter U8) := run (it.slice.val.length+1) it

theorem source (it : core.slice.iter.Iter U8) :
 any it=CheckpointBytes4Ops.headerAny it := loop _ it

theorem next_frame (it rest : core.slice.iter.Iter U8) (value : Option U8)
 (step : core.slice.iter.IteratorSliceIter.next it=ok (value,rest)) :
 rest.slice=it.slice := by
 unfold core.slice.iter.IteratorSliceIter.next at step
 split at step <;> cases step <;> rfl

/-- No byte of the backing slice is modified on any returning path. -/
theorem frame (n : Nat) (it out : core.slice.iter.Iter U8) (hit : Bool)
 (returned : run n it=ok (hit,out)) : out.slice=it.slice := by
 induction n generalizing it with
 | zero => cases returned;rfl
 | succ n ih =>
   unfold run at returned
   cases step : core.slice.iter.IteratorSliceIter.next it with
   | fail err => simp only [step,bind_tc_fail] at returned;cases returned
   | div => simp only [step,bind_tc_div] at returned;cases returned
   | ok pair =>
     rcases pair with ⟨value,rest⟩
     have fr:=next_frame it rest value step
     rw [step] at returned
     simp only [bind_tc_ok] at returned
     cases value with
     | none => cases returned;exact fr
     | some b =>
       change (if b != 0#u8 then ok (true,rest) else run n rest)=ok (hit,out) at returned
       split at returned
       · cases returned;exact fr
       · exact (ih rest returned).trans fr

/-- Exactly the same complete Bool/post-iterator pair at the existing resume
external slot; no root hypothesis and no opaque callback Result premise. -/
theorem installed {H : Type} (d : NID_ResumeEmission.aspis_core.digest.Digest32 H)
 (it : core.slice.iter.Iter U8) :
 NIL_FreshOps.any
  (NID_ResumeEmission.verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool d)
  it ()=any it := (NIL_HeaderAny.source d it).trans (source it).symm

#print axioms loop
#print axioms source
#print axioms next_frame
#print axioms frame
#print axioms installed
end NJJ_Any
