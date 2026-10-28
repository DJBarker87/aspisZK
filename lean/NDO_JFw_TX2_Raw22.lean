import NDO_JFw_TX2_Raw21
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7737303599#u64 5576662683#u64 13569409087#u64 10520247992#u64⟩,⟨pack 5532954889#u64 3871671539#u64 10703909594#u64 8017079108#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9792231287#u64 6593072721#u64 17695316860#u64 12128830605#u64⟩,⟨pack 8139270253#u64 7262111851#u64 15760486681#u64 14130762130#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 3831105949220081704#u64 1374237501844137026#u64 8403150256965968375#u64 3070530044165593144#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 651333885#u32 1978379752#u32 1026286559#u32 709814346#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 651333885#u32) (JFs_TX2_RawMath.extend 1978379752#u32) (JFs_TX2_RawMath.extend 1026286559#u32) (JFs_TX2_RawMath.extend 709814346#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 651333885#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 651333885#u32) (JFs_TX2_RawMath.extend 1978379752#u32) (JFs_TX2_RawMath.extend 1026286559#u32) (JFs_TX2_RawMath.extend 709814346#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1978379752#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 651333885#u32) (JFs_TX2_RawMath.extend 1978379752#u32) (JFs_TX2_RawMath.extend 1026286559#u32) (JFs_TX2_RawMath.extend 709814346#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1026286559#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 651333885#u32) (JFs_TX2_RawMath.extend 1978379752#u32) (JFs_TX2_RawMath.extend 1026286559#u32) (JFs_TX2_RawMath.extend 709814346#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 709814346#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2111832427473911446#u64 4715281728165768185#u64 7499524912021629415#u64 8555914993549047705#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 651333885#u32 1978379752#u32 1026286559#u32 709814346#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 651333885#u32) (JFs_TX2_RawMath.extend 1978379752#u32) (JFs_TX2_RawMath.extend 1026286559#u32) (JFs_TX2_RawMath.extend 709814346#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 651333885#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 651333885#u32) (JFs_TX2_RawMath.extend 1978379752#u32) (JFs_TX2_RawMath.extend 1026286559#u32) (JFs_TX2_RawMath.extend 709814346#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1978379752#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 651333885#u32) (JFs_TX2_RawMath.extend 1978379752#u32) (JFs_TX2_RawMath.extend 1026286559#u32) (JFs_TX2_RawMath.extend 709814346#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1026286559#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 651333885#u32) (JFs_TX2_RawMath.extend 1978379752#u32) (JFs_TX2_RawMath.extend 1026286559#u32) (JFs_TX2_RawMath.extend 709814346#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 709814346#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails10.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails10.value2_2=
      ok (.Ok (pack 651333885#u32 1978379752#u32 1026286559#u32 709814346#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (651333885<2147483647 ∧ 1978379752<2147483647) ∧ (1026286559<2147483647 ∧ 709814346<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 651333885#u32 1978379752#u32 1026286559#u32 709814346#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7737303599#u64 5576662683#u64 13569409087#u64 10520247992#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 651333885#u32 1978379752#u32 1026286559#u32 709814346#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5532954889#u64 3871671539#u64 10703909594#u64 8017079108#u64⟩ raw1=_
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
end AspisR1.JFw_TX2_Raw22
end
