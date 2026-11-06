import NJX_RecipientBody
import NJB_PreparedCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_RecipientRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (O D ocells dcells dc)
def zero : Fin 2 → NQ := fun _=>FIq_Native.field.QM31.ZERO
def reference (recipient : Option D) (o : O) (high : NQ) : Result (Fin 2 → NQ) :=
 match recipient with
 | none=>ok zero
 | some d=>NJX_RecipientBody.reference high (ocells o) (dcells d)
def cohort (recipient : Option D) (o : O) (high : NQ) : Result (Fin 2 → NQ) :=
 match recipient with
 | none=>ok zero
 | some d=>NJX_LeftRoot.cohort high o d
/-- NJL_K061/062 Some/None control, SAME actual constructor high and all9
cache words for both groups, ordered2group replies and complete ZERO arm. -/
def Cut (recipient : Option D) (o : O) (high : NQ) (news groups : Nat)
 (seenHigh : NQ) (seenO : O) (seenD : Option D) (cache : Option FIv_PreparedNew.NP)
 (seenCache : Fin 2 → Option FIv_PreparedNew.NP) (child out : Fin 2 → NQ) : Prop :=
 match recipient with
 | none=>news=0 ∧ groups=0 ∧ out=zero
 | some d=>news=1 ∧ groups=2 ∧ seenHigh=high ∧ seenO=o ∧ seenD=some d ∧ out=child ∧ ∃ p,cache=some p ∧ ∀ g,seenCache g=some p
/-- Full246: SAME constructor+4residual/pack/product+4residual/pack/product,
all actual child Results; canonical NONE needs no digest-domain premise. -/
theorem source (recipient : Option D) (o : O) (high : NQ) (hh : Canon high)
 (ho : FIw_ArrayValue.canonical o) (hd : ∀ d,recipient=some d→dc d) :
 ∃ out cache,reference recipient o high=ok out ∧ cohort recipient o high=ok out ∧
 (∀ g,Canon (out g)) ∧
 Cut recipient o high (if recipient.isSome then 1 else 0) (if recipient.isSome then 2 else 0) high o recipient cache (fun _=>cache) out out ∧
 (∀ d,recipient=some d→∃ p : NJX_DigestPacket.Packet high (ocells o) (dcells d),out=p.out ∧
 FIq_Native.field.PreparedQm31Multiplier.new high=ok p.prepared ∧
 (∀ g,NJX_RecipientBody.group p.prepared (ocells o) (dcells d) g=ok (out g))) := by
 cases recipient with
 | none=>
   refine ⟨zero,none,rfl,rfl,fun _=>FIv_NativeValue.zero.1,⟨rfl,rfl,rfl⟩,?_⟩
   intro d h;cases h
 | some d=>
   obtain ⟨p,_,mc⟩ := NJX_LeftRoot.source high o d hh ho (hd d rfl)
   refine ⟨p.out,some p.prepared,NJX_RecipientBody.source p,mc,p.out_canonical,⟨rfl,rfl,rfl,rfl,rfl,rfl,p.prepared,rfl,fun _=>rfl⟩,?_⟩
   intro d' h
   cases Option.some.inj h
   exact ⟨p,rfl,p.constructor,fun g=>NJX_RecipientBody.group_source p g⟩
#print source
#print axioms source
end AspisR1.NJX_RecipientRoot
end
