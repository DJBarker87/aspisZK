import NDO_JFz_TX2_Q1_Raw21
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7544711480#u64 4015559827#u64 11792102452#u64 9051911277#u64⟩,⟨pack 5385875366#u64 1668920626#u64 10979118100#u64 4352149603#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 11435966557#u64 6354687758#u64 16166247216#u64 10686861342#u64⟩,⟨pack 7797421759#u64 4460679251#u64 15601639816#u64 9864093771#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4476287811882968845#u64 1451776613604705333#u64 8830407393098618242#u64 3140510117419069713#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1297982732#u32 1416913335#u32 605966413#u32 1273584862#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1297982732#u32) (JFs_TX2_RawMath.extend 1416913335#u32) (JFs_TX2_RawMath.extend 605966413#u32) (JFs_TX2_RawMath.extend 1273584862#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1297982732#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1297982732#u32) (JFs_TX2_RawMath.extend 1416913335#u32) (JFs_TX2_RawMath.extend 605966413#u32) (JFs_TX2_RawMath.extend 1273584862#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1416913335#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1297982732#u32) (JFs_TX2_RawMath.extend 1416913335#u32) (JFs_TX2_RawMath.extend 605966413#u32) (JFs_TX2_RawMath.extend 1273584862#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 605966413#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1297982732#u32) (JFs_TX2_RawMath.extend 1416913335#u32) (JFs_TX2_RawMath.extend 605966413#u32) (JFs_TX2_RawMath.extend 1273584862#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1273584862#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4297209426105320624#u64 4913658812961207761#u64 8114140441517991417#u64 8768611699015605285#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1297982732#u32 1416913335#u32 605966413#u32 1273584862#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1297982732#u32) (JFs_TX2_RawMath.extend 1416913335#u32) (JFs_TX2_RawMath.extend 605966413#u32) (JFs_TX2_RawMath.extend 1273584862#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1297982732#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1297982732#u32) (JFs_TX2_RawMath.extend 1416913335#u32) (JFs_TX2_RawMath.extend 605966413#u32) (JFs_TX2_RawMath.extend 1273584862#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1416913335#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1297982732#u32) (JFs_TX2_RawMath.extend 1416913335#u32) (JFs_TX2_RawMath.extend 605966413#u32) (JFs_TX2_RawMath.extend 1273584862#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 605966413#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1297982732#u32) (JFs_TX2_RawMath.extend 1416913335#u32) (JFs_TX2_RawMath.extend 605966413#u32) (JFs_TX2_RawMath.extend 1273584862#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1273584862#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails11.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails11.value2_2=
      ok (.Ok (pack 1297982732#u32 1416913335#u32 605966413#u32 1273584862#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1297982732<2147483647 ∧ 1416913335<2147483647) ∧ (605966413<2147483647 ∧ 1273584862<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1297982732#u32 1416913335#u32 605966413#u32 1273584862#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7544711480#u64 4015559827#u64 11792102452#u64 9051911277#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1297982732#u32 1416913335#u32 605966413#u32 1273584862#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5385875366#u64 1668920626#u64 10979118100#u64 4352149603#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q1_Raw22
end
