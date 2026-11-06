import NKI_DigestPacked
import NKI_TargetConstructors
import NKI_RightTarget
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_BindingPacket
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (O D dc)
/-- All target/constructor/pack/product child laws at SAME actual inputs;
full2cell raw equality to the emitted cohort, for either offset/right flag. -/
theorem source (high : NQ) (o : O) (d : D) (start : Usize) (right : Bool)
 (hb : start.val+8≤16) (hh : Canon high) (ho : FIw_ArrayValue.canonical o) (hd : dc d) :
 ∃ t : NKI_DigestTargets.Packet d right,
 ∃ p : NJX_DigestPacket.Packet high (NKI_DigestView.opened o start hb) (NKI_DigestTargets.cells t),
 NJX_DigestPacket.reference high (NKI_DigestView.opened o start hb) (NKI_DigestTargets.cells t)=ok p.out ∧
 NKI_DigestPacked.cohort high o d start right=ok p.out := by
 have target : ∃ t : NKI_DigestTargets.Packet d right,True := by
  cases right
  · exact NKI_TargetConstructors.left d hd
  · exact NKI_RightTarget.source d hd
 obtain ⟨t,_⟩ := target
 obtain ⟨p,cp,co⟩ := NKI_DigestPacked.source high o d start right hb hh ho hd
  (NKI_DigestTargets.cells t) (NKI_DigestTargets.canonical t hd) (NKI_DigestTargets.values t)
 exact ⟨t,p,cp,co⟩
#print source
#print axioms source
end AspisR1.NKI_BindingPacket
end
