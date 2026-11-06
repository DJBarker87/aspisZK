import NIW_AlignRegularStream
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularExecution
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignRegularStream
variable [FIo_Native.Allocation]

/-- Source-ordered execution with a local chronological observation stream.
Child calls are the emitted frozen source calls, not selected model packets.
The log is outside Result so the entered fail/div event is retained. -/
def execute (w : W) (alpha : Slice E) (f : Slice U8) (ap0 ap1 : Powers) :
 List Usize → Scratch → Parts → Result NHM_RegularKinds.Reply × List Event
 | [],s,p => (ok (.Ok (),s,p),[])
 | k::ks,s,p =>
  let observed := FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p
  let event : Event := ⟨k,s,p,observed⟩
  match observed with
  | fail e => (fail e,[event])
  | div => (div,[event])
  | ok (.Err e,after,post) => (ok (.Err e,after,post),[event])
  | ok (.Ok (),after,post) =>
    let tail := execute w alpha f ap0 ap1 ks after post
    (tail.1,event::tail.2)

/-- Erasing observations recovers the exact source body, including all aborts
and mutable states; no execution equation is an input premise. -/
theorem erase (w : W) (alpha : Slice E) (f : Slice U8) (ap0 ap1 : Powers)
 (ks : List Usize) (s : Scratch) (p : Parts) :
 (execute w alpha f ap0 ap1 ks s p).1=
 NHM_RegularKinds.go (fun k s p=>FIo_Native.weights.process_kind w k alpha f
  2#usize 64#usize ap0 ap1 s p) ks s p := by
 induction ks generalizing s p with
 | nil => rfl
 | cons k ks ih =>
  cases call : FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p with
  | fail e => simp only [execute,call,NHM_RegularKinds.go];rfl
  | div => simp only [execute,call,NHM_RegularKinds.go];rfl
  | ok value =>
   rcases value with ⟨reply,after,post⟩
   cases reply with
   | Err e => simp only [execute,call,NHM_RegularKinds.go];rfl
   | Ok u =>
    cases u
    rw [NHM_RegularKinds.after_ok _ k ks s after p post call]
    simpa only [execute,call] using ih after post

theorem source (w : W) (shared : Bool) (alpha : Slice E) (f : Slice U8)
 (ap0 ap1 : Powers) (s : Scratch) (p : Parts) :
 FIo_Native.weights.process_regular_kinds w shared alpha f 2#usize 64#usize ap0 ap1 s p=
 (execute w alpha f ap0 ap1 (NHM_RegularKinds.kinds shared) s p).1 := by
 rw [NHM_RegularKinds.cohort]
 exact (erase w alpha f ap0 ap1 _ s p).symm

#print axioms erase
#print axioms source
end AspisR1.NIW_AlignRegularExecution
