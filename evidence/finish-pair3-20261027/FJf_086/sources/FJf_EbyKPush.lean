import FJf_EbyKCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_EbyKPush
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE qm wide)
open FJf_EbyKCodec (Bound model scalar)

theorem mul_scalar {K : Type} [CommRing K] (r : K) (a b c : K) :
    (⟨a,b⟩ : QuadraticAlgebra K r 0)*⟨c,0⟩=⟨a*c,b*c⟩ := by
  apply QuadraticAlgebra.ext <;>
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,mul_zero,zero_mul,add_zero,zero_add]

theorem value (self next : FIo_Native.fast_pairing.EbyKDot) (v : NE) (q : NQ)
    (hv : FIo_WideValues.Canon v) (hq : FIo_QMValues.Canon q) (bound : Bound self)
    (run : FIo_Native.fast_pairing.EbyKDot.push self v q=ok (.Ok (),next)) :
    next.count.val=self.count.val+1 ∧ Bound next ∧
      model next=model self+decodeWide (wide v)*scalar q := by
  unfold FIo_Native.fast_pairing.EbyKDot.push at run
  split at run
  · cases run
  · rename_i full
    have hn : self.count.val < 4096 := by
      unfold FIo_Native.fast_pairing.MAX_TERMS at full
      scalar_tac
    have r0 : Array.index_usize (FJf_EbyKCodec.halves v) 0#usize=ok (JFs_TX2_CheckedQ.value v.c0) := rfl
    have r1 : Array.index_usize (FJf_EbyKCodec.halves v) 1#usize=ok (JFs_TX2_CheckedQ.value v.c1) := rfl
    simp only [FJf_EbyKCodec.from_wide,r0,r1,JFs_TX2_CheckedQ.source q hq,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,lift] at run
    obtain ⟨d0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨d1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have vp0 := FJf_DotMeaning.push self.c0 d0 _ _
      (FJf_EbyKCodec.canon v.c0 hv.1) (FJf_EbyKCodec.canon q hq) self.count.val hn bound.1 h0
    have vp1 := FJf_DotMeaning.push self.c1 d1 _ _
      (FJf_EbyKCodec.canon v.c1 hv.2) (FJf_EbyKCodec.canon q hq) self.count.val hn bound.2 h1
    have size : 8192≤UScalar.size .Usize := by
      rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
      rcases System.Platform.numBits_eq with h|h <;> simp [h]
    have count : (Usize.wrapping_add self.count 1#usize).val=self.count.val+1 := by
      rw [Usize.wrapping_add_val_eq,show (1#usize).val=1 from by decide,Nat.mod_eq_of_lt (by omega)]
    refine ⟨count,?_,?_⟩
    · change FJf_DotBound.Bound d0 (Usize.wrapping_add self.count 1#usize).val ∧
        FJf_DotBound.Bound d1 (Usize.wrapping_add self.count 1#usize).val
      rw [count]
      exact ⟨vp0.1,vp1.1⟩
    · change (⟨FJf_RawDecode.dot d0,FJf_RawDecode.dot d1⟩ : AspisWideTower.WideExact)=
        (⟨FJf_RawDecode.dot self.c0,FJf_RawDecode.dot self.c1⟩ : AspisWideTower.WideExact)+
        (⟨decodeQM (qm v.c0),decodeQM (qm v.c1)⟩ : AspisWideTower.WideExact)*⟨decodeQM (qm q),0⟩
      have hm : (⟨decodeQM (qm v.c0),decodeQM (qm v.c1)⟩ : AspisWideTower.WideExact)*⟨decodeQM (qm q),0⟩=
          ⟨decodeQM (qm v.c0)*decodeQM (qm q),decodeQM (qm v.c1)*decodeQM (qm q)⟩ := mul_scalar _ _ _ _
      rw [hm]
      apply QuadraticAlgebra.ext
      · change FJf_RawDecode.dot d0=FJf_RawDecode.dot self.c0+decodeQM (qm v.c0)*decodeQM (qm q)
        simpa only [FJf_EbyKCodec.decoded] using vp0.2
      · change FJf_RawDecode.dot d1=FJf_RawDecode.dot self.c1+decodeQM (qm v.c1)*decodeQM (qm q)
        simpa only [FJf_EbyKCodec.decoded] using vp1.2
#print axioms mul_scalar
#print axioms value
end AspisR1.FJf_EbyKPush
end
