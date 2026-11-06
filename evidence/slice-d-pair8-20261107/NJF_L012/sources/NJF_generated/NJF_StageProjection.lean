import NJF_SharedContinuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_StageProjection
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NJF_RegularCut NJF_RegularInstantiation NJF_SharedContinuation

def observed (c : Context) (scratch : Scratch) (parts : Parts) : Result State × List Nat :=
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

theorem erase (c : Context) (scratch : Scratch) (parts : Parts) :
 (observed c scratch parts).1=stage c scratch parts := by
 unfold observed stage
 cases hc : commonReply c with
 | fail err => rfl
 | div => rfl
 | ok value =>
  rcases value with ⟨owner,cells⟩
  cases hp : FIo_Native.weights.shared_partials c.f.value cells with
  | fail err => rfl
  | div => rfl
  | ok partials =>
   cases partials with
   | Err err => rfl
   | Ok values =>
    cases hh : FIo_Native.weights.shared_high values owner c.ap0.value c.ap1.value parts <;> rfl

#print axioms erase
end AspisR1.NJF_StageProjection
