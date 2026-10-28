import NDO_JFz_TX2_Q1_Raw31
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails11
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8003695068#u64 4470370051#u64 12704318339#u64 6214038759#u64⟩,⟨pack 6722345324#u64 4762476579#u64 11035810519#u64 6200146678#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 12137647787#u64 6072561620#u64 18948567940#u64 8779716961#u64⟩,⟨pack 9964725239#u64 7205369830#u64 17004162567#u64 10698667449#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4673936460329307115#u64 1041646419277392133#u64 9817923717067384013#u64 2595825029004440130#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1072352022#u32 860964525#u32 1360713590#u32 610109220#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1072352022#u32) (JFs_TX2_RawMath.extend 860964525#u32) (JFs_TX2_RawMath.extend 1360713590#u32) (JFs_TX2_RawMath.extend 610109220#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1072352022#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1072352022#u32) (JFs_TX2_RawMath.extend 860964525#u32) (JFs_TX2_RawMath.extend 1360713590#u32) (JFs_TX2_RawMath.extend 610109220#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 860964525#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1072352022#u32) (JFs_TX2_RawMath.extend 860964525#u32) (JFs_TX2_RawMath.extend 1360713590#u32) (JFs_TX2_RawMath.extend 610109220#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1360713590#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1072352022#u32) (JFs_TX2_RawMath.extend 860964525#u32) (JFs_TX2_RawMath.extend 1360713590#u32) (JFs_TX2_RawMath.extend 610109220#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 610109220#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4924087041246301285#u64 3509887688594446144#u64 11217023849128793003#u64 7390446224098308965#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1072352022#u32 860964525#u32 1360713590#u32 610109220#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1072352022#u32) (JFs_TX2_RawMath.extend 860964525#u32) (JFs_TX2_RawMath.extend 1360713590#u32) (JFs_TX2_RawMath.extend 610109220#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1072352022#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1072352022#u32) (JFs_TX2_RawMath.extend 860964525#u32) (JFs_TX2_RawMath.extend 1360713590#u32) (JFs_TX2_RawMath.extend 610109220#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 860964525#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1072352022#u32) (JFs_TX2_RawMath.extend 860964525#u32) (JFs_TX2_RawMath.extend 1360713590#u32) (JFs_TX2_RawMath.extend 610109220#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1360713590#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1072352022#u32) (JFs_TX2_RawMath.extend 860964525#u32) (JFs_TX2_RawMath.extend 1360713590#u32) (JFs_TX2_RawMath.extend 610109220#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 610109220#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails11.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails11.value2_3=
      ok (.Ok (pack 1072352022#u32 860964525#u32 1360713590#u32 610109220#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1072352022<2147483647 ∧ 860964525<2147483647) ∧ (1360713590<2147483647 ∧ 610109220<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1072352022#u32 860964525#u32 1360713590#u32 610109220#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 8003695068#u64 4470370051#u64 12704318339#u64 6214038759#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1072352022#u32 860964525#u32 1360713590#u32 610109220#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6722345324#u64 4762476579#u64 11035810519#u64 6200146678#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q1_Raw32
end
