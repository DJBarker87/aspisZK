import RPu_JFs_TX2_CheckedQ
import NDO_JFs_TX2_DotPush
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_EbyKPush
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap

theorem source (s : FIo_Native.fast_pairing.EbyKDot) (v : FIo_Install.NE)
    (q : FIo_Native.aspis_core.field.QM31) (hq : FIo_QMValues.Canon q)
    (count : s.count.val<256) :
    ∃ out, FIo_Native.fast_pairing.EbyKDot.push s v q=ok (.Ok (),out) ∧ out.count.val=s.count.val+1 := by
  let a := pack v.c0.c0.a v.c0.c0.b v.c0.c1.a v.c0.c1.b
  let b := pack v.c1.c0.a v.c1.c0.b v.c1.c1.a v.c1.c1.b
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide v=ok (Array.make 2#usize [a,b]) := by rfl
  have r0 : Array.index_usize (Array.make 2#usize [a,b]) 0#usize=ok a := rfl
  have r1 : Array.index_usize (Array.make 2#usize [a,b]) 1#usize=ok b := rfl
  have full : ¬s.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold FIo_Native.fast_pairing.MAX_TERMS
    scalar_tac
  obtain ⟨d0,h0⟩ := JFs_TX2_DotPush.source s.c0 a (JFs_TX2_CheckedQ.value q)
  obtain ⟨d1,h1⟩ := JFs_TX2_DotPush.source s.c1 b (JFs_TX2_CheckedQ.value q)
  refine ⟨⟨d0,d1,Usize.wrapping_add s.count 1#usize⟩,?_,?_⟩
  · simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,
      JFs_TX2_CheckedQ.source q hq,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,h0,h1,lift]
  · change (Usize.wrapping_add s.count 1#usize).val=s.count.val+1
    exact Port3_Wrapping.increment s.count count

#print axioms source
end AspisR1.JFs_TX2_EbyKPush
end
