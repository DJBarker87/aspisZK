import NIL_FreshOps
set_option autoImplicit false
noncomputable section
namespace NIL_HeaderAny
open Aeneas Aeneas.Std Result
open NIL_FreshOps AspisR1 NID_ResumeEmission

theorem loop {H : Type} (d : aspis_core.digest.Digest32 H) (n : Nat)
 (it : core.slice.iter.Iter U8) :
 anyLoop (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool d)
 n it ()=CheckpointBytes4Ops.headerLoop n it := by
 induction n generalizing it with
 | zero => rfl
 | succ n ih =>
   unfold anyLoop CheckpointBytes4Ops.headerLoop
   cases h : core.slice.iter.IteratorSliceIter.next it with
   | fail err => rfl
   | div => rfl
   | ok x =>
     rcases x with ⟨value,rest⟩
     cases value with
     | none => rfl
     | some b =>
       simp only [bind_tc_ok,
        verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool,
        verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool.call_mut]
       dsimp only
       rw [ih]

theorem source {H : Type} (d : aspis_core.digest.Digest32 H)
 (it : core.slice.iter.Iter U8) :
 NIL_FreshOps.any (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool d)
 it ()=CheckpointBytes4Ops.headerAny it := loop d _ it
#print axioms loop
#print axioms source
end NIL_HeaderAny
