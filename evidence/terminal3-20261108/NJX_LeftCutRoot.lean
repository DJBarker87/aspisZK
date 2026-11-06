import NJX_LeftRoot
import NJX_DigestCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_LeftCutRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (O D ocells dcells dc)
/-- Positive242 root: reviewed K001/K002 cut, full actual child packet,
complete return and SAME emitted/cohort pack. No successful-child premise. -/
theorem source (high : NQ) (o : O) (d : D) (hh : Canon high)
 (ho : FIw_ArrayValue.canonical o) (hd : dc d) :
 ∃ p : NJX_DigestPacket.Packet high (ocells o) (dcells d),
 NJX_DigestPacket.reference high (ocells o) (dcells d)=ok p.out ∧
 NJX_LeftRoot.cohort high o d=ok p.out ∧
 NJX_DigestCut.Cut high (ocells o) (dcells d) p.prepared (fun i=>FIw_ScalarArithmetic.lifted (dcells d i))
  p.residual p.packed p.out p.out (NJX_DigestCut.log p) 21 := by
 obtain ⟨p,call,cohort⟩ := NJX_LeftRoot.source high o d hh ho hd
 exact ⟨p,call,cohort,NJX_DigestCut.source p⟩
#print source
#print axioms source
end AspisR1.NJX_LeftCutRoot
end
