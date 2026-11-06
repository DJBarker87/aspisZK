import NJF_RegularCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_RegularInstantiation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl AspisR1Stage2
open NJF_RegularCut
variable [FIo_Native.Allocation]

/-- Actual decoded child result, not an independently selected native log. -/
def regularReply (c : Context) (before : Scratch) : Result NHM_RegularKinds.Reply :=
 FIo_Native.weights.process_regular_kinds c.w.value (NGM_GuardExact.guard c.w.value 2#usize)
  c.alpha.value.to_slice c.f.value 2#usize 64#usize c.ap0.value c.ap1.value before initial

def commonReply (c : Context) : Result (W × CommonCells) :=
 (NIW_AlignCommonCollect.collect c.w.value 17
  ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ)).1

/-- Child clauses are discharged by construction at the reached logged arguments.
Unentered replies use div as irrelevant data; no existence/success is assumed. -/
def instantiate (c : Context) (before : Scratch) : Log :=
 let regular := regularReply c before
 match regular with
 | ok (.Ok (),_,parts) => if NGM_GuardExact.guard c.w.value 2#usize then
   let common := commonReply c
   match common with
   | ok (owner,cells) =>
     let partialReply := FIo_Native.weights.shared_partials c.f.value cells
     match partialReply with
     | ok (.Ok values) =>
       ⟨regular,common,partialReply,FIo_Native.weights.shared_high values owner c.ap0.value c.ap1.value parts⟩
     | _ => ⟨regular,common,partialReply,div⟩
   | _ => ⟨regular,common,div,div⟩
  else ⟨regular,div,div,div⟩
 | _ => ⟨regular,div,div,div⟩

/-- Independent source-ordered stage evaluator: child post-states determine the
arguments of the next entered child. All outer aborts retain their prefix. -/
def segment (c : Context) (before : Scratch) : Result State × List Nat :=
 match regularReply c before with
 | fail err => (fail err,[0])
 | div => (div,[0])
 | ok (reply,scratch,parts) => match reply with
   | .Err err => (ok (.Err err,scratch,parts),[0])
   | .Ok _ => if NGM_GuardExact.guard c.w.value 2#usize then
     match commonReply c with
     | fail err => (fail err,[0,1])
     | div => (div,[0,1])
     | ok (owner,cells) => match FIo_Native.weights.shared_partials c.f.value cells with
       | fail err => (fail err,[0,1,2])
       | div => (div,[0,1,2])
       | ok (.Err err) => (ok (.Err err,scratch,parts),[0,1,2])
       | ok (.Ok values) => match FIo_Native.weights.shared_high values owner c.ap0.value c.ap1.value parts with
         | fail err => (fail err,[0,1,2,3])
         | div => (div,[0,1,2,3])
         | ok (reply,after) => (ok (reply,scratch,after),[0,1,2,3])
    else (ok (.Ok (),scratch,parts),[0])

/-- The (y)(3) direction. No RegularProjection, PairWitness, child-success or
endpoint-equality premise is used. -/
theorem source (c : Context) (before : Scratch) :
 G (NGM_GuardExact.guard c.w.value 2#usize) (instantiate c before)=segment c before := by
 unfold instantiate segment
 cases hr : regularReply c before with
 | fail err => rfl
 | div => rfl
 | ok value =>
  rcases value with ⟨reply,scratch,parts⟩
  cases reply with
  | Err err => rfl
  | Ok unit =>
   cases unit
   cases hs : NGM_GuardExact.guard c.w.value 2#usize with
   | false => rfl
   | true =>
    cases hc : commonReply c with
    | fail err => rfl
    | div => rfl
    | ok value =>
     rcases value with ⟨owner,cells⟩
     cases hp : FIo_Native.weights.shared_partials c.f.value cells with
     | fail err => simp only [hp,G,ite_true,ite_false]
     | div => simp only [hp,G,ite_true,ite_false]
     | ok partials => cases partials <;> simp only [hp,G,ite_true,ite_false]

#print source
#print axioms source
end AspisR1.NJF_RegularInstantiation
