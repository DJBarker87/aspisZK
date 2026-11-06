import NJX_LeftRoot
import NJX_DigestCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_CarryRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (O D ocells dcells dc)
def zero : Fin 2 → NQ := fun _=>FIq_Native.field.QM31.ZERO
def reference (carry : Nat) (high : NQ) (o : O) (d : D) : Result (Fin 2 → NQ) :=
 if carry<20 then NJX_DigestPacket.reference high (ocells o) (dcells d) else ok zero
def cohort (carry : Nat) (high : NQ) (o : O) (d : D) : Result (Fin 2 → NQ) :=
 if carry<20 then NJX_LeftRoot.cohort high o d else ok zero
/-- Complete245: native carry guard and full ZERO inactive arm; active arm
uses exact21-call SAME left body and every child law internally. -/
theorem source (carry : Nat) (high : NQ) (o : O) (d : D) (hh : Canon high)
 (ho : FIw_ArrayValue.canonical o) (hd : dc d) :
 ∃ out,reference carry high o d=ok out ∧ cohort carry high o d=ok out ∧
 (∀ g,Canon (out g)) ∧
 (if carry<20 then ∃ p : NJX_DigestPacket.Packet high (ocells o) (dcells d),out=p.out ∧
  NJX_DigestCut.Cut high (ocells o) (dcells d) p.prepared (fun i=>FIw_ScalarArithmetic.lifted (dcells d i))
   p.residual p.packed p.out out (NJX_DigestCut.log p) 21 else out=zero) := by
 by_cases active : carry<20
 · obtain ⟨p,pc,mc⟩ := NJX_LeftRoot.source high o d hh ho hd
   refine ⟨p.out,by simpa only [reference,if_pos active] using pc,by simpa only [cohort,if_pos active] using mc,p.out_canonical,?_⟩
   rw [if_pos active]
   exact ⟨p,rfl,NJX_DigestCut.source p⟩
 · refine ⟨zero,by simp only [reference,if_neg active],by simp only [cohort,if_neg active],fun _=>FIv_NativeValue.zero.1,?_⟩
   rw [if_neg active]
#print source
#print axioms source
end AspisR1.NJX_CarryRoot
end
