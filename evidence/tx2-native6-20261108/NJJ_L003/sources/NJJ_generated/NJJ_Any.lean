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
 | n+1,it =>
   if h : it.i < it.slice.val.length then
    let b := it.slice.val[it.i]
    let rest : core.slice.iter.Iter U8 := ⟨it.slice,it.i+1⟩
    if b != 0#u8 then ok (true,rest) else run n rest
   else ok (false,it)

theorem loop (n : Nat) (it : core.slice.iter.Iter U8) :
 run n it=CheckpointBytes4Ops.headerLoop n it := by
 induction n generalizing it with
 | zero => rfl
 | succ n ih =>
   simp only [run,CheckpointBytes4Ops.headerLoop,core.slice.iter.IteratorSliceIter.next,
    Slice.len]
   split <;> simp_all only [bind_tc_ok]

def any (it : core.slice.iter.Iter U8) := run (it.slice.val.length+1) it

theorem source (it : core.slice.iter.Iter U8) :
 any it=CheckpointBytes4Ops.headerAny it := loop _ it

/-- No byte of the backing slice is modified on any returning path. -/
theorem frame (n : Nat) (it out : core.slice.iter.Iter U8) (hit : Bool)
 (returned : run n it=ok (hit,out)) : out.slice=it.slice := by
 induction n generalizing it with
 | zero => cases returned;rfl
 | succ n ih =>
   unfold run at returned
   split at returned
   · split at returned
     · cases returned;rfl
     · exact ih _ returned
   · cases returned;rfl

/-- Exactly the same complete Bool/post-iterator pair at the existing resume
external slot; no root hypothesis and no opaque callback Result premise. -/
theorem installed {H : Type} (d : NID_ResumeEmission.aspis_core.digest.Digest32 H)
 (it : core.slice.iter.Iter U8) :
 NIL_FreshOps.any
  (NID_ResumeEmission.verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool d)
  it ()=any it := (NIL_HeaderAny.source d it).trans (source it).symm

#print axioms loop
#print axioms source
#print axioms frame
#print axioms installed
end NJJ_Any
