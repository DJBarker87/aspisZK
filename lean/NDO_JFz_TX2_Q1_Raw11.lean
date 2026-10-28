import NDO_JFz_TX2_Q1_Raw10
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3098985233#u64 2257182111#u64 5815130307#u64 3806736873#u64⟩,⟨pack 1951567687#u64 2175265159#u64 5225648234#u64 4308043983#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7256764747#u64 4879262454#u64 13581847621#u64 6418515281#u64⟩,⟨pack 6478674624#u64 4635015765#u64 10496492366#u64 6124455666#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 8081995058989016795#u64 2681496093134198877#u64 12210776179921382152#u64 4661205814970464108#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2016440547#u32 1019372649#u32 701920109#u32 121841408#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016440547#u32) (JFs_TX2_RawMath.extend 1019372649#u32) (JFs_TX2_RawMath.extend 701920109#u32) (JFs_TX2_RawMath.extend 121841408#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2016440547#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016440547#u32) (JFs_TX2_RawMath.extend 1019372649#u32) (JFs_TX2_RawMath.extend 701920109#u32) (JFs_TX2_RawMath.extend 121841408#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1019372649#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016440547#u32) (JFs_TX2_RawMath.extend 1019372649#u32) (JFs_TX2_RawMath.extend 701920109#u32) (JFs_TX2_RawMath.extend 121841408#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 701920109#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016440547#u32) (JFs_TX2_RawMath.extend 1019372649#u32) (JFs_TX2_RawMath.extend 701920109#u32) (JFs_TX2_RawMath.extend 121841408#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 121841408#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5667485450932601727#u64 1140625923552587351#u64 9992222413826535476#u64 1866390932915928271#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2016440547#u32 1019372649#u32 701920109#u32 121841408#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016440547#u32) (JFs_TX2_RawMath.extend 1019372649#u32) (JFs_TX2_RawMath.extend 701920109#u32) (JFs_TX2_RawMath.extend 121841408#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2016440547#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016440547#u32) (JFs_TX2_RawMath.extend 1019372649#u32) (JFs_TX2_RawMath.extend 701920109#u32) (JFs_TX2_RawMath.extend 121841408#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1019372649#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016440547#u32) (JFs_TX2_RawMath.extend 1019372649#u32) (JFs_TX2_RawMath.extend 701920109#u32) (JFs_TX2_RawMath.extend 121841408#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 701920109#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2016440547#u32) (JFs_TX2_RawMath.extend 1019372649#u32) (JFs_TX2_RawMath.extend 701920109#u32) (JFs_TX2_RawMath.extend 121841408#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 121841408#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails11.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails11.value1_1=
      ok (.Ok (pack 2016440547#u32 1019372649#u32 701920109#u32 121841408#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2016440547<2147483647 ∧ 1019372649<2147483647) ∧ (701920109<2147483647 ∧ 121841408<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2016440547#u32 1019372649#u32 701920109#u32 121841408#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3098985233#u64 2257182111#u64 5815130307#u64 3806736873#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2016440547#u32 1019372649#u32 701920109#u32 121841408#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 1951567687#u64 2175265159#u64 5225648234#u64 4308043983#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q1_Raw11
end
