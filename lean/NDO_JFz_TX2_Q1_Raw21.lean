import NDO_JFz_TX2_Q1_Raw20
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3483105489#u64 2401195620#u64 6192161075#u64 5114471605#u64⟩,⟨pack 2717320988#u64 1257415999#u64 4810509362#u64 2998012971#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7544711480#u64 4015559827#u64 11792102452#u64 9051911277#u64⟩,⟨pack 5385875366#u64 1668920626#u64 10979118100#u64 4352149603#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5312827272034600933#u64 1574257365581527224#u64 11471714172344001660#u64 4326330109043417881#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 507761969#u32 728338262#u32 1483761710#u32 1061805110#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 507761969#u32) (JFs_TX2_RawMath.extend 728338262#u32) (JFs_TX2_RawMath.extend 1483761710#u32) (JFs_TX2_RawMath.extend 1061805110#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 507761969#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 507761969#u32) (JFs_TX2_RawMath.extend 728338262#u32) (JFs_TX2_RawMath.extend 1483761710#u32) (JFs_TX2_RawMath.extend 1061805110#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 728338262#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 507761969#u32) (JFs_TX2_RawMath.extend 728338262#u32) (JFs_TX2_RawMath.extend 1483761710#u32) (JFs_TX2_RawMath.extend 1061805110#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1483761710#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 507761969#u32) (JFs_TX2_RawMath.extend 728338262#u32) (JFs_TX2_RawMath.extend 1483761710#u32) (JFs_TX2_RawMath.extend 1061805110#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1061805110#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4764489444756630714#u64 591330088132110537#u64 9743357254349801545#u64 1665009564682019191#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 507761969#u32 728338262#u32 1483761710#u32 1061805110#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 507761969#u32) (JFs_TX2_RawMath.extend 728338262#u32) (JFs_TX2_RawMath.extend 1483761710#u32) (JFs_TX2_RawMath.extend 1061805110#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 507761969#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 507761969#u32) (JFs_TX2_RawMath.extend 728338262#u32) (JFs_TX2_RawMath.extend 1483761710#u32) (JFs_TX2_RawMath.extend 1061805110#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 728338262#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 507761969#u32) (JFs_TX2_RawMath.extend 728338262#u32) (JFs_TX2_RawMath.extend 1483761710#u32) (JFs_TX2_RawMath.extend 1061805110#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1483761710#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 507761969#u32) (JFs_TX2_RawMath.extend 728338262#u32) (JFs_TX2_RawMath.extend 1483761710#u32) (JFs_TX2_RawMath.extend 1061805110#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1061805110#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails11.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails11.value1_2=
      ok (.Ok (pack 507761969#u32 728338262#u32 1483761710#u32 1061805110#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (507761969<2147483647 ∧ 728338262<2147483647) ∧ (1483761710<2147483647 ∧ 1061805110<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 507761969#u32 728338262#u32 1483761710#u32 1061805110#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3483105489#u64 2401195620#u64 6192161075#u64 5114471605#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 507761969#u32 728338262#u32 1483761710#u32 1061805110#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2717320988#u64 1257415999#u64 4810509362#u64 2998012971#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q1_Raw21
end
