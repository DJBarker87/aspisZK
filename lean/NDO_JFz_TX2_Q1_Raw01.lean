import NDO_JFz_TX2_Q1_Raw00
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2941027537#u64 2542853526#u64 5649913087#u64 3289050270#u64⟩,⟨pack 3365591051#u64 755013948#u64 4746405645#u64 3575943989#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5227148167#u64 3616575798#u64 11858209401#u64 6158914364#u64⟩,⟨pack 5834797948#u64 1269378977#u64 11558592292#u64 4715669831#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4728502493238355656#u64 406328963925315468#u64 12172609597897407899#u64 2736954957350005390#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 98599104#u32 194226097#u32 1771038364#u32 874811890#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 98599104#u32) (JFs_TX2_RawMath.extend 194226097#u32) (JFs_TX2_RawMath.extend 1771038364#u32) (JFs_TX2_RawMath.extend 874811890#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 98599104#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 98599104#u32) (JFs_TX2_RawMath.extend 194226097#u32) (JFs_TX2_RawMath.extend 1771038364#u32) (JFs_TX2_RawMath.extend 874811890#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 194226097#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 98599104#u32) (JFs_TX2_RawMath.extend 194226097#u32) (JFs_TX2_RawMath.extend 1771038364#u32) (JFs_TX2_RawMath.extend 874811890#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1771038364#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 98599104#u32) (JFs_TX2_RawMath.extend 194226097#u32) (JFs_TX2_RawMath.extend 1771038364#u32) (JFs_TX2_RawMath.extend 874811890#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 874811890#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4628702599711044214#u64 148867408772649512#u64 10090086436322367433#u64 1134177810524669095#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 98599104#u32 194226097#u32 1771038364#u32 874811890#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 98599104#u32) (JFs_TX2_RawMath.extend 194226097#u32) (JFs_TX2_RawMath.extend 1771038364#u32) (JFs_TX2_RawMath.extend 874811890#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 98599104#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 98599104#u32) (JFs_TX2_RawMath.extend 194226097#u32) (JFs_TX2_RawMath.extend 1771038364#u32) (JFs_TX2_RawMath.extend 874811890#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 194226097#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 98599104#u32) (JFs_TX2_RawMath.extend 194226097#u32) (JFs_TX2_RawMath.extend 1771038364#u32) (JFs_TX2_RawMath.extend 874811890#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1771038364#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 98599104#u32) (JFs_TX2_RawMath.extend 194226097#u32) (JFs_TX2_RawMath.extend 1771038364#u32) (JFs_TX2_RawMath.extend 874811890#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 874811890#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails11.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails11.value1_0=
      ok (.Ok (pack 98599104#u32 194226097#u32 1771038364#u32 874811890#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (98599104<2147483647 ∧ 194226097<2147483647) ∧ (1771038364<2147483647 ∧ 874811890<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 98599104#u32 194226097#u32 1771038364#u32 874811890#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2941027537#u64 2542853526#u64 5649913087#u64 3289050270#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 98599104#u32 194226097#u32 1771038364#u32 874811890#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3365591051#u64 755013948#u64 4746405645#u64 3575943989#u64⟩ raw1=_
    simp only [raw1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add before.count 1#usize=after.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment before.count (by unfold before;decide)
  rw [inc]
#print axioms pair0
#print axioms pair1
#print axioms source
end AspisR1.JFz_TX2_Q1_Raw01
end
