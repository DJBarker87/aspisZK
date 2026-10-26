import JFv_QMCanonical
import JFv_SelectedBytes
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
  have total : r1_wire.ValidatedRecord.decode_k_value self byteOffset value offset
      ⦃ result => ∃ q,result=.Ok q ⦄ := by
    unfold r1_wire.ValidatedRecord.decode_k_value
    step*
    all_goals try (solve | simp only [Slice.length,bytes_post,List.length_drop]; omega)
    case length => rw [s_post];rfl
    case canon =>
      have length : s.length=16 := by rw [s_post];rfl
      have fits : start.val+16 ≤ bytes.length := by
        simp only [Slice.length,bytes_post,List.length_drop];omega
      have align : start.val%4=0 := by omega
      have can : canonical (bytesOf bytes.val) := by rw [bytes_post];exact canon
      refine JFv_SelectedBytes.canonical_slice bytes s start.val 16 length fits align (by decide) can ?_
      intro j hj
      subst s
      change ([i1,i3,i5,i7,i9,i11,i13,i15,i17,i19,i21,i23,i25,i27,i29,i31] : List U8)[j]'_ = _
      interval_cases j <;>
        simp only [List.getElem_cons_zero,List.getElem_cons_succ,
            i1_post,i3_post,i5_post,i7_post,i9_post,i11_post,i13_post,i15_post,
            i17_post,i19_post,i21_post,i23_post,i25_post,i27_post,i29_post,i31_post,
            i2_post,i4_post,i6_post,i8_post,i10_post,i12_post,i14_post,i16_post,
            i18_post,i20_post,i22_post,i24_post,i26_post,i28_post,i30_post,Nat.add_zero]
    all_goals simp only [o_post,core.option.Option.ok_or]
    all_goals exact ⟨_,rfl⟩
  obtain ⟨result,call,q,same⟩ := WP.spec_imp_exists total
  exact ⟨q,by rw [same] at call;exact call⟩

#print axioms payload
#print axioms success
end AspisR1.JFv_Value
