import NDO_JFw_TX2_Raw30
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6063838767#u64 3156527730#u64 4393837268#u64 4150636049#u64⟩,⟨pack 4005165594#u64 1462898421#u64 6667467438#u64 3445886947#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8807624361#u64 5555186220#u64 10680298618#u64 6620035662#u64⟩,⟨pack 8158134413#u64 2458619915#u64 11609625846#u64 5925111184#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4244289691299175041#u64 2623797044869164213#u64 10971293229218008966#u64 4259932387111299166#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 69156310#u32 1363214210#u32 1941246937#u32 740091329#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69156310#u32) (JFs_TX2_RawMath.extend 1363214210#u32) (JFs_TX2_RawMath.extend 1941246937#u32) (JFs_TX2_RawMath.extend 740091329#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 69156310#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69156310#u32) (JFs_TX2_RawMath.extend 1363214210#u32) (JFs_TX2_RawMath.extend 1941246937#u32) (JFs_TX2_RawMath.extend 740091329#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1363214210#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69156310#u32) (JFs_TX2_RawMath.extend 1363214210#u32) (JFs_TX2_RawMath.extend 1941246937#u32) (JFs_TX2_RawMath.extend 740091329#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1941246937#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69156310#u32) (JFs_TX2_RawMath.extend 1363214210#u32) (JFs_TX2_RawMath.extend 1941246937#u32) (JFs_TX2_RawMath.extend 740091329#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 740091329#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4329501590418247920#u64 895545055249319455#u64 9551424106876397323#u64 1608863900061551435#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 69156310#u32 1363214210#u32 1941246937#u32 740091329#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69156310#u32) (JFs_TX2_RawMath.extend 1363214210#u32) (JFs_TX2_RawMath.extend 1941246937#u32) (JFs_TX2_RawMath.extend 740091329#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 69156310#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69156310#u32) (JFs_TX2_RawMath.extend 1363214210#u32) (JFs_TX2_RawMath.extend 1941246937#u32) (JFs_TX2_RawMath.extend 740091329#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1363214210#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69156310#u32) (JFs_TX2_RawMath.extend 1363214210#u32) (JFs_TX2_RawMath.extend 1941246937#u32) (JFs_TX2_RawMath.extend 740091329#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1941246937#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69156310#u32) (JFs_TX2_RawMath.extend 1363214210#u32) (JFs_TX2_RawMath.extend 1941246937#u32) (JFs_TX2_RawMath.extend 740091329#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 740091329#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails10.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails10.value1_3=
      ok (.Ok (pack 69156310#u32 1363214210#u32 1941246937#u32 740091329#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (69156310<2147483647 ∧ 1363214210<2147483647) ∧ (1941246937<2147483647 ∧ 740091329<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 69156310#u32 1363214210#u32 1941246937#u32 740091329#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6063838767#u64 3156527730#u64 4393837268#u64 4150636049#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 69156310#u32 1363214210#u32 1941246937#u32 740091329#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4005165594#u64 1462898421#u64 6667467438#u64 3445886947#u64⟩ raw1=_
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
end AspisR1.JFw_TX2_Raw31
end
