import NKI_AppendBits
import NKR_DigestChildren
import RPv_FIz_PublicDigest
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestReads
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (decode K)

theorem cell {n : Usize} (a : Array NQ n) (i : Fin n.val) :
 decode (NJB_ArrayCarrier.cell a i)=FIv_NativeArray.value a i.val := by
 unfold NJB_ArrayCarrier.cell FIv_NativeArray.value
 rw [List.getElem?_eq_getElem (by rw [a.property];exact i.isLt)]
 rfl

theorem target (d : NJX_DigestCohort.D) (right : Bool) (i : Fin 8) :
 NKI_DigestView.target d right i=FIy_DigestLane.target d right i.val := by
 unfold NKI_DigestView.target FIy_DigestLane.target FIy_DigestTarget.value NJX_DigestCohort.dcells NJB_ArrayCarrier.cell
 rw [List.getElem?_eq_getElem (by rw [d.property];exact i.isLt)]
 rfl

theorem opened (o : NJX_DigestCohort.O) (start : Usize) (hb : start.val+8≤16) (i : Fin 8) :
 decode (NKI_DigestView.opened o start hb i)=FIv_NativeArray.value o (start.val+i.val) :=
 cell o _

theorem residual {index level frontier o high}
 (p : NKI_AppendPacket.Packet index level frontier o high) (i : Fin 8) :
 NKI_AppendMeaning.residual p i=FIy_DigestLane.increment high o
  (NKI_AppendPacket.start (NKI_AppendPacket.emptySide index level)).val p.expected
  (NKI_AppendPacket.emptySide index level) i.val := by
 unfold NKI_AppendMeaning.residual FIy_DigestLane.increment
 rw [NKI_DigestTargets.values,opened,target]

#print axioms cell
#print axioms target
#print axioms opened
#print axioms residual
end AspisR1.NKR_DigestReads
end
