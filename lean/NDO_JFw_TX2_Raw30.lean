import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6063838767#u64 3156527730#u64 4393837268#u64 4150636049#u64⟩,⟨pack 4005165594#u64 1462898421#u64 6667467438#u64 3445886947#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 8547460174287305396#u64 2899610361959928301#u64 9242536561124079299#u64 5416468131462732783#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1889883511#u32 70292776#u32 500617354#u32 1878153621#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1889883511#u32) (JFs_TX2_RawMath.extend 70292776#u32) (JFs_TX2_RawMath.extend 500617354#u32) (JFs_TX2_RawMath.extend 1878153621#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1889883511#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1889883511#u32) (JFs_TX2_RawMath.extend 70292776#u32) (JFs_TX2_RawMath.extend 500617354#u32) (JFs_TX2_RawMath.extend 1878153621#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 70292776#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1889883511#u32) (JFs_TX2_RawMath.extend 70292776#u32) (JFs_TX2_RawMath.extend 500617354#u32) (JFs_TX2_RawMath.extend 1878153621#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 500617354#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1889883511#u32) (JFs_TX2_RawMath.extend 70292776#u32) (JFs_TX2_RawMath.extend 500617354#u32) (JFs_TX2_RawMath.extend 1878153621#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1878153621#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5369383530154571356#u64 2383241348192672819#u64 10843003086955695863#u64 5550195586031389934#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1889883511#u32 70292776#u32 500617354#u32 1878153621#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1889883511#u32) (JFs_TX2_RawMath.extend 70292776#u32) (JFs_TX2_RawMath.extend 500617354#u32) (JFs_TX2_RawMath.extend 1878153621#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1889883511#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1889883511#u32) (JFs_TX2_RawMath.extend 70292776#u32) (JFs_TX2_RawMath.extend 500617354#u32) (JFs_TX2_RawMath.extend 1878153621#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 70292776#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1889883511#u32) (JFs_TX2_RawMath.extend 70292776#u32) (JFs_TX2_RawMath.extend 500617354#u32) (JFs_TX2_RawMath.extend 1878153621#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 500617354#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1889883511#u32) (JFs_TX2_RawMath.extend 70292776#u32) (JFs_TX2_RawMath.extend 500617354#u32) (JFs_TX2_RawMath.extend 1878153621#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1878153621#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails10.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails10.value0_3=
      ok (.Ok (pack 1889883511#u32 70292776#u32 500617354#u32 1878153621#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1889883511<2147483647 ∧ 70292776<2147483647) ∧ (500617354<2147483647 ∧ 1878153621<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1889883511#u32 70292776#u32 500617354#u32 1878153621#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1889883511#u32 70292776#u32 500617354#u32 1878153621#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw1=_
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
end AspisR1.JFw_TX2_Raw30
end
