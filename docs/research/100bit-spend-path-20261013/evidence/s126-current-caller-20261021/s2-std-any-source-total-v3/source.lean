import S2StdAnySourceV1
import S2CheckpointGuardTransportV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisS2StdAnySource
open AspisS2OwnedStage1.CheckpointGuardTransport

/-- The exact emitted byte predicate, retaining its callback state. -/
def nonzeroPredicate : core.ops.function.FnMut Unit U8 Bool where
  FnOnceInst := {call_once := fun _ byte => ok (byte != 0#u8)}
  call_mut := fun state byte => ok (byte != 0#u8,state)

/-- A next-step specification over the actual two pointer fields. The pointer
carriers remain arbitrary, with no source instance silently installed. -/
def NextReads {P Q : Type}
    (next : SourceIter P Q → Result ((Option U8) × SourceIter P Q))
    (remaining : P → Q → List U8) : Prop :=
  ∀ ptr endp, ∃ ptr' endp',
    next ⟨ptr,endp,()⟩ = ok ((remaining ptr endp).head?,⟨ptr',endp',()⟩) ∧
    remaining ptr' endp' = (remaining ptr endp).tail

private theorem anyLoop_unfold {T P Q F : Type}
    (next : SourceIter P Q → Result ((Option T) × SourceIter P Q))
    (callback : core.ops.function.FnMut F T Bool) (ptr : P) (endp : Q) (state : F) :
    anyLoop next callback ptr endp state = (do
      let step ← anyBody next callback ptr endp state
      match step with
      | .done out => ok out
      | .cont (ptr',endp',state') => anyLoop next callback ptr' endp' state') := by
  unfold anyLoop
  rw [loop.eq_def]
  cases hstep : anyBody next callback ptr endp state with
  | fail e => rfl
  | div => rfl
  | ok step =>
    cases step with
    | done out => rfl
    | cont item => rcases item with ⟨ptr',endp',state'⟩; rfl

/-- TOTAL for the actual extracted any loop under its explicit next instance.
Induction is over remaining bytes, not bounded execution or numeral reduction. -/
theorem anyLoop_total {P Q : Type}
    (next : SourceIter P Q → Result ((Option U8) × SourceIter P Q))
    (remaining : P → Q → List U8) (reads : NextReads next remaining)
    (bytes : List U8) (ptr : P) (endp : Q) (view : remaining ptr endp = bytes) :
    ∃ ptr' endp', anyLoop next nonzeroPredicate ptr endp () =
      ok (ptr',endp',if stdAny bytes then some true else none) := by
  induction bytes generalizing ptr endp with
  | nil =>
    obtain ⟨ptr',endp',hnext,_⟩ := reads ptr endp
    rw [view] at hnext
    refine ⟨ptr',endp',?_⟩
    rw [anyLoop_unfold]
    simp only [Aeneas.Std.uncurry,anyBody,hnext,bind_tc_ok,List.head?_nil,stdAny,Bool.false_eq_true,if_false]
  | cons byte rest ih =>
    obtain ⟨ptr',endp',hnext,hrest⟩ := reads ptr endp
    rw [view] at hnext hrest
    simp only [List.tail_cons] at hrest
    by_cases zero : byte = 0#u8
    · obtain ⟨ptrOut,endOut,hrun⟩ := ih ptr' endp' hrest
      refine ⟨ptrOut,endOut,?_⟩
      rw [anyLoop_unfold]
      simpa only [Aeneas.Std.uncurry,anyBody,hnext,bind_tc_ok,List.head?_cons,nonzeroPredicate,
        zero,bne_self_eq_false,Bool.false_eq_true,if_false,stdAny,if_true] using hrun
    · refine ⟨ptr',endp',?_⟩
      rw [anyLoop_unfold]
      simp only [Aeneas.Std.uncurry,anyBody,hnext,bind_tc_ok,List.head?_cons,nonzeroPredicate,
        bne_iff_ne.mpr zero,if_true,stdAny,if_neg zero]

/-- The complete emitted any returns the same boolean as the owned scan.
Both pointer fields of the emitted iterator remain in the returned witness. -/
theorem sourceAny_total {P Q : Type}
    (next : SourceIter P Q → Result ((Option U8) × SourceIter P Q))
    (remaining : P → Q → List U8) (reads : NextReads next remaining)
    (iter : SourceIter P Q) :
    ∃ iterOut, sourceAny next nonzeroPredicate iter () =
      ok (stdAny (remaining iter.ptr iter.end_or_len),iterOut) := by
  obtain ⟨ptr',endp',hrun⟩ := anyLoop_total next remaining reads
    (remaining iter.ptr iter.end_or_len) iter.ptr iter.end_or_len rfl
  refine ⟨⟨ptr',endp',()⟩,?_⟩
  unfold sourceAny
  rw [hrun,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  cases hbool : stdAny (remaining iter.ptr iter.end_or_len) <;> rfl

/-- Contextual equality with the complete checked owned checkpoint scan.
The arbitrary continuation can retain full SDK state, errors and oracle logs.
The explicit native next/byte-view instance is the only iterator premise. -/
theorem guard_eq_owned {P Q A : Type}
    (next : SourceIter P Q → Result ((Option U8) × SourceIter P Q))
    (remaining : P → Q → List U8) (reads : NextReads next remaining)
    (iter : SourceIter P Q) (bytes : alloc.vec.Vec U8)
    (view : remaining iter.ptr iter.end_or_len=bytes.val) (reject resume : Result A) :
    (do let (hit,_) ← sourceAny next nonzeroPredicate iter ()
        if hit then reject else resume) =
    (do let hit ← AspisS2OwnedStage1.owned_checkpoint_nonzero bytes
        if hit then reject else resume) := by
  obtain ⟨iterOut,hrun⟩ := sourceAny_total next remaining reads iter
  rw [hrun,owned_eq_std,view]
  rfl

#print axioms anyLoop_total
#print axioms sourceAny_total
#print axioms guard_eq_owned
end AspisS2StdAnySource
