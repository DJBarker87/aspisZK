import NKL_NativeGuard
import NKL_ScanModel
set_option autoImplicit false
noncomputable section
namespace NKL_ScanSequence
open Aeneas Aeneas.Std Result AspisR1 NKL_Checks NKL_ScanAtoms NKL_NativeGuard
abbrev Bytes := List U8

def run : List Check→Reply×List Check
 | []=>(.Ok (),[])
 | c::cs=>if nativeGuard c then
   let tail:=run cs
   (tail.1,c::tail.2)
  else (.Err .Parse,[c])

/-- Reviewed single-entered-call G cut, instantiated with the actual CLOSED
child in ScanAtoms. The readonly assertion denotes the arbitrary-cell frame,
not pointer-to-payload inference. Source contexts remain inside Check. -/
structure Cut (c : Check) (out : Reply) (events : List Check) (pre post : Bytes) : Prop where
 result : out=NKB_CanonicalOpening.reply (nativeGuard c)
 calls : events=[c]
 frame : post=pre

/-- Source-ordered native cuts. Each continuation is available only on Ok;
Err terminates immediately, so no later check or event can be selected. -/
inductive Invoke : List Check→Reply→List Check→Bytes→Bytes→Prop where
 | done (bytes:Bytes) : Invoke [] (.Ok ()) [] bytes bytes
 | next (c:Check) (cs:List Check) (first tail:List Check) (pre mid post:Bytes)
   (out:Reply) (cut:Cut c (.Ok ()) first pre mid)
   (rest:Invoke cs out tail mid post) : Invoke (c::cs) out (first++tail) pre post
 | reject (c:Check) (cs:List Check) (events:List Check) (pre post:Bytes)
   (cut:Cut c (.Err .Parse) events pre post) : Invoke (c::cs) (.Err .Parse) events pre post

theorem exact {xs:List Check} {out:Reply} {events:List Check} {pre post:Bytes}
 (native:Invoke xs out events pre post) :
 out=(run xs).1 ∧ events=(run xs).2 ∧ post=pre := by
 induction native with
 | done bytes=>exact ⟨rfl,rfl,rfl⟩
 | next c cs first tail pre mid post out cut rest ih=>
   have valid:nativeGuard c=true := by
    have h:=cut.result
    cases hval:nativeGuard c <;> simp_all [NKB_CanonicalOpening.reply]
   simp only [run,valid,if_true]
   exact ⟨ih.1,by rw [cut.calls,ih.2.1];rfl,ih.2.2.trans cut.frame⟩
 | reject c cs events pre post cut=>
   have valid:nativeGuard c=false := by
    have h:=cut.result
    cases hval:nativeGuard c <;> simp_all [NKB_CanonicalOpening.reply]
   simp only [run,valid,Bool.false_eq_true,if_false]
   exact ⟨rfl,cut.calls,cut.frame⟩

theorem result (xs:List Check) :
 (run xs).1=NKB_CanonicalOpening.reply (xs.all nativeGuard) := by
 induction xs with
 | nil=>rfl
 | cons c cs ih=>
   cases h:nativeGuard c <;> simp only [run,h,Bool.false_eq_true,if_false,if_true,
    List.all_cons,Bool.false_and,Bool.true_and,ih]
   rfl

theorem prefix (xs:List Check) : ∃ suffix,(run xs).2++suffix=xs := by
 induction xs with
 | nil=>exact ⟨[],rfl⟩
 | cons c cs ih=>
   obtain ⟨suffix,eq⟩:=ih
   cases h:nativeGuard c
   · exact ⟨cs,by simp [run,h]⟩
   · exact ⟨suffix,by simp only [run,h,if_true,List.cons_append,eq]⟩

theorem success_trace (xs:List Check) (success:(run xs).1=.Ok ()) : (run xs).2=xs := by
 induction xs with
 | nil=>rfl
 | cons c cs ih=>
   cases h:nativeGuard c
   · simp [run,h] at success
   · simp only [run,h,if_true] at success ⊢
     exact congrArg (List.cons c) (ih success)

/-- First rejected call is the last event, and all preceding checks nativeGuard.
This retains exact order rather than asserting only rejection existence. -/
theorem rejection_trace (xs:List Check) (failure:(run xs).1=.Err .Parse) :
 ∃ before bad suffix,xs=before++bad::suffix ∧
 (run xs).2=before++[bad] ∧ before.all nativeGuard=true ∧ nativeGuard bad=false := by
 induction xs with
 | nil=>cases failure
 | cons c cs ih=>
   cases h:nativeGuard c
   · exact ⟨[],c,cs,rfl,by simp [run,h],rfl,h⟩
   · simp only [run,h,if_true] at failure ⊢
     obtain ⟨before,bad,suffix,order,events,prior,err⟩:=ih failure
     exact ⟨c::before,bad,suffix,by rw [order];rfl,by rw [events];rfl,
      by simp [h,prior],err⟩

set_option pp.proofs false
#print exact
#print axioms exact
#print axioms result
#print axioms prefix
#print axioms success_trace
#print axioms rejection_trace
end NKL_ScanSequence
end
