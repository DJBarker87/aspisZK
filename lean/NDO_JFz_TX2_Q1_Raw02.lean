import NDO_JFz_TX2_Q1_Raw01
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5227148167#u64 3616575798#u64 11858209401#u64 6158914364#u64⟩,⟨pack 5834797948#u64 1269378977#u64 11558592292#u64 4715669831#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9133553315#u64 5385553741#u64 18032933507#u64 9840427842#u64⟩,⟨pack 9780835996#u64 5383461831#u64 17550966854#u64 11443650989#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4615698352862560440#u64 1953074587021019165#u64 10232679023428190548#u64 4123086520506590550#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1910912708#u32 1724366754#u32 1861584959#u32 412322717#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1910912708#u32) (JFs_TX2_RawMath.extend 1724366754#u32) (JFs_TX2_RawMath.extend 1861584959#u32) (JFs_TX2_RawMath.extend 412322717#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1910912708#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1910912708#u32) (JFs_TX2_RawMath.extend 1724366754#u32) (JFs_TX2_RawMath.extend 1861584959#u32) (JFs_TX2_RawMath.extend 412322717#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1724366754#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1910912708#u32) (JFs_TX2_RawMath.extend 1724366754#u32) (JFs_TX2_RawMath.extend 1861584959#u32) (JFs_TX2_RawMath.extend 412322717#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1861584959#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1910912708#u32) (JFs_TX2_RawMath.extend 1724366754#u32) (JFs_TX2_RawMath.extend 1861584959#u32) (JFs_TX2_RawMath.extend 412322717#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 412322717#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4817001812114597856#u64 6592064127198330203#u64 12675688688162320826#u64 11335410356297525524#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1910912708#u32 1724366754#u32 1861584959#u32 412322717#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1910912708#u32) (JFs_TX2_RawMath.extend 1724366754#u32) (JFs_TX2_RawMath.extend 1861584959#u32) (JFs_TX2_RawMath.extend 412322717#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1910912708#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1910912708#u32) (JFs_TX2_RawMath.extend 1724366754#u32) (JFs_TX2_RawMath.extend 1861584959#u32) (JFs_TX2_RawMath.extend 412322717#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1724366754#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1910912708#u32) (JFs_TX2_RawMath.extend 1724366754#u32) (JFs_TX2_RawMath.extend 1861584959#u32) (JFs_TX2_RawMath.extend 412322717#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1861584959#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1910912708#u32) (JFs_TX2_RawMath.extend 1724366754#u32) (JFs_TX2_RawMath.extend 1861584959#u32) (JFs_TX2_RawMath.extend 412322717#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 412322717#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails11.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails11.value2_0=
      ok (.Ok (pack 1910912708#u32 1724366754#u32 1861584959#u32 412322717#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1910912708<2147483647 ∧ 1724366754<2147483647) ∧ (1861584959<2147483647 ∧ 412322717<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1910912708#u32 1724366754#u32 1861584959#u32 412322717#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5227148167#u64 3616575798#u64 11858209401#u64 6158914364#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1910912708#u32 1724366754#u32 1861584959#u32 412322717#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5834797948#u64 1269378977#u64 11558592292#u64 4715669831#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q1_Raw02
end
