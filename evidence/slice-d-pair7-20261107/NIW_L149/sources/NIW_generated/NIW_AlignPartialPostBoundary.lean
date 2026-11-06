import NIW_AlignSharedPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPartialPostBoundary
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

def Call (c : Context) : Option (Result RP) :=
 match (NIW_AlignCommonCollect.collect c.w.value 17
  ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ)).1 with
 | fail _ => none
 | div => none
 | ok (_,cells) => some (FIo_Native.weights.shared_partials c.f.value cells)

theorem observed (c : Context) (parts : Parts) :
 (NIW_AlignSharedPhase.run c parts).2.partialReply=Call c := by
 cases common : (NIW_AlignCommonCollect.collect c.w.value 17
  ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ)).1 with
 | fail err => simp only [NIW_AlignSharedPhase.run,common,Call]
 | div => simp only [NIW_AlignSharedPhase.run,common,Call]
 | ok value =>
  rcases value with ⟨owner,cells⟩
  cases partialCall : FIo_Native.weights.shared_partials c.f.value cells with
  | fail err => simp only [NIW_AlignSharedPhase.run,common,partialCall,Call]
  | div => simp only [NIW_AlignSharedPhase.run,common,partialCall,Call]
  | ok reply => simp only [NIW_AlignSharedPhase.run,common,partialCall,Call]

def Post : Option (Result RP) → Prop
 | some (ok (.Ok values)) => canonical values
 | _ => True

theorem source (c : Context) (parts : Parts) : Post (NIW_AlignSharedPhase.run c parts).2.partialReply := by
 rw [observed]
 unfold Call
 cases common : (NIW_AlignCommonCollect.collect c.w.value 17
  ({start:=0#usize,«end»:=16#usize},Array.repeat 16#usize NHX_FilledZero.zeroQ)).1 with
 | fail err => trivial
 | div => trivial
 | ok value =>
  rcases value with ⟨owner,cells⟩
  cases partialCall : FIo_Native.weights.shared_partials c.f.value cells with
  | fail err => trivial
  | div => trivial
  | ok reply =>
   cases reply with
   | Err err => trivial
   | Ok values => exact NIG_PairFrames.partials c.f.value cells values partialCall

#print axioms observed
#print axioms source
end AspisR1.NIW_AlignPartialPostBoundary
