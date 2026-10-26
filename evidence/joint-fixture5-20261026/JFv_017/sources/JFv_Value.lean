import JFv_QMCanonical
set_option autoImplicit false
namespace AspisR1.JFv_Value
open Aeneas Aeneas.Std Result WP
open AspisR1DecodeKFullV10
open OraclePortCompactDraft MultiproofConeCanonical

@[step] theorem payload (self : r1_wire.ValidatedRecord) (bound : 5 ≤ self.framed.length) :
    r1_wire.ValidatedRecord.payload self ⦃ bytes => bytes.val=self.framed.val.drop 5 ⦄ := by
  unfold r1_wire.ValidatedRecord.payload
  step* <;> scalar_tac

theorem success (self : r1_wire.ValidatedRecord) (byteOffset value offset : Usize)
    (bound : 5+byteOffset.val+32*value.val+16 ≤ self.framed.length)
    (small : self.framed.length ≤ 20000)
    (aligned : byteOffset.val%4=0)
    (offsetBound : offset.val+value.val ≤ Usize.max)
    (canon : canonical (bytesOf (self.framed.val.drop 5))) :
    ∃ q,r1_wire.ValidatedRecord.decode_k_value self byteOffset value offset=ok (.Ok q) := by
  apply WP.spec_imp_exists
  unfold r1_wire.ValidatedRecord.decode_k_value
  step*

#print axioms payload
#print axioms success
end AspisR1.JFv_Value
