import NDO_JFw_TX2_Raw10
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 1124426164#u64 2505825052#u64 5774722422#u64 4677425203#u64⟩,⟨pack 2149288668#u64 2262126725#u64 2962290080#u64 3339306344#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4871738743#u64 3604150452#u64 13178457049#u64 7803498471#u64⟩,⟨pack 5417749459#u64 3691455832#u64 9258062350#u64 3866116044#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 7228540490532623669#u64 1020899873465118603#u64 11397013422910955454#u64 2695750795881718163#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1423223756#u32 262156717#u32 234369701#u32 184835074#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1423223756#u32) (JFs_TX2_RawMath.extend 262156717#u32) (JFs_TX2_RawMath.extend 234369701#u32) (JFs_TX2_RawMath.extend 184835074#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1423223756#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1423223756#u32) (JFs_TX2_RawMath.extend 262156717#u32) (JFs_TX2_RawMath.extend 234369701#u32) (JFs_TX2_RawMath.extend 184835074#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 262156717#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1423223756#u32) (JFs_TX2_RawMath.extend 262156717#u32) (JFs_TX2_RawMath.extend 234369701#u32) (JFs_TX2_RawMath.extend 184835074#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 234369701#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1423223756#u32) (JFs_TX2_RawMath.extend 262156717#u32) (JFs_TX2_RawMath.extend 234369701#u32) (JFs_TX2_RawMath.extend 184835074#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 184835074#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5466505060048889392#u64 510191922821247776#u64 9835026339160640445#u64 1108169607545648542#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1423223756#u32 262156717#u32 234369701#u32 184835074#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1423223756#u32) (JFs_TX2_RawMath.extend 262156717#u32) (JFs_TX2_RawMath.extend 234369701#u32) (JFs_TX2_RawMath.extend 184835074#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1423223756#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1423223756#u32) (JFs_TX2_RawMath.extend 262156717#u32) (JFs_TX2_RawMath.extend 234369701#u32) (JFs_TX2_RawMath.extend 184835074#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 262156717#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1423223756#u32) (JFs_TX2_RawMath.extend 262156717#u32) (JFs_TX2_RawMath.extend 234369701#u32) (JFs_TX2_RawMath.extend 184835074#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 234369701#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1423223756#u32) (JFs_TX2_RawMath.extend 262156717#u32) (JFs_TX2_RawMath.extend 234369701#u32) (JFs_TX2_RawMath.extend 184835074#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 184835074#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails10.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails10.value1_1=
      ok (.Ok (pack 1423223756#u32 262156717#u32 234369701#u32 184835074#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1423223756<2147483647 ∧ 262156717<2147483647) ∧ (234369701<2147483647 ∧ 184835074<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1423223756#u32 262156717#u32 234369701#u32 184835074#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 1124426164#u64 2505825052#u64 5774722422#u64 4677425203#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1423223756#u32 262156717#u32 234369701#u32 184835074#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2149288668#u64 2262126725#u64 2962290080#u64 3339306344#u64⟩ raw1=_
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
end AspisR1.JFw_TX2_Raw11
end
