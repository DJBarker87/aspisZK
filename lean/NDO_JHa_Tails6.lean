import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFw_TX2_CellUnique
import NDO_JGw_Tails06
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Tails6
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def s0_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s0_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 4517346142#u64 2245834454#u64 5330859312#u64 3648439051#u64)⟩,⟨(pack 2420045151#u64 2860949244#u64 4661497803#u64 3738507224#u64)⟩,1#usize⟩
def raw0_0_0 : Array U64 4#usize := (pack 5969056016830335418#u64 4611581453251998986#u64 9637102090530765467#u64 4248231619628712639#u64)
theorem pair0_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1438120579#u32 1179126529#u32 431598766#u32 978748296#u32)=ok raw0_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_0
def raw0_0_1 : Array U64 4#usize := (pack 3787498364965169659#u64 2316938623065770031#u64 8690544051199592513#u64 6395793626249576195#u64)
theorem pair0_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1438120579#u32 1179126529#u32 431598766#u32 978748296#u32)=ok raw0_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_1
theorem push0_0 : FIo_Native.fast_pairing.EbyKDot.push s0_0 JFw_TX2_P28.value
    JGw_Tails06.value0_0=ok (.Ok (),s0_1) := by
  have full : ¬s0_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value0_0=
      ok (.Ok (pack 1438120579#u32 1179126529#u32 431598766#u32 978748296#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1438120579<2147483647 ∧ 1179126529<2147483647) ∧ (431598766<2147483647 ∧ 978748296<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1438120579#u32 1179126529#u32 431598766#u32 978748296#u32)=ok s0_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_0.c0 raw0_0_0=_
    simp only [s0_0,raw0_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1438120579#u32 1179126529#u32 431598766#u32 978748296#u32)=ok s0_1.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_0_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_0.c1 raw0_0_1=_
    simp only [s0_0,raw0_0_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s0_0.count 1#usize=s0_1.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s0_0.count (by unfold s0_0;decide)
  rw [inc]
#print axioms push0_0
def s0_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 8449604732#u64 5149825399#u64 11377722784#u64 8677299028#u64)⟩,⟨(pack 5470977652#u64 4676701941#u64 9699383853#u64 6017908940#u64)⟩,2#usize⟩
def raw0_1_0 : Array U64 4#usize := (pack 7199982228830064061#u64 2043594440523564544#u64 10744892066106491809#u64 6960382593905578523#u64)
theorem pair0_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1508183171#u32 782361957#u32 512294406#u32 1900434874#u32)=ok raw0_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_0
def raw0_1_1 : Array U64 4#usize := (pack 5396586947949918876#u64 865973261357355978#u64 9345158077191992030#u64 2568669913318255002#u64)
theorem pair0_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1508183171#u32 782361957#u32 512294406#u32 1900434874#u32)=ok raw0_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_1
theorem push0_1 : FIo_Native.fast_pairing.EbyKDot.push s0_1 JFw_TX2_P26.value
    JGw_Tails06.value1_0=ok (.Ok (),s0_2) := by
  have full : ¬s0_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value1_0=
      ok (.Ok (pack 1508183171#u32 782361957#u32 512294406#u32 1900434874#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1508183171<2147483647 ∧ 782361957<2147483647) ∧ (512294406<2147483647 ∧ 1900434874<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1508183171#u32 782361957#u32 512294406#u32 1900434874#u32)=ok s0_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_1.c0 raw0_1_0=_
    simp only [s0_1,raw0_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1508183171#u32 782361957#u32 512294406#u32 1900434874#u32)=ok s0_2.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_1_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_1.c1 raw0_1_1=_
    simp only [s0_1,raw0_1_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s0_1.count 1#usize=s0_2.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s0_1.count (by unfold s0_1;decide)
  rw [inc]
#print axioms push0_1
def s0_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 10470397769#u64 6313200034#u64 16529327104#u64 10521127003#u64)⟩,⟨(pack 7537303405#u64 8107875266#u64 14439836617#u64 9402601758#u64)⟩,3#usize⟩
def raw0_2_0 : Array U64 4#usize := (pack 3994426613878275870#u64 950735320720363186#u64 8494651117396368898#u64 1599842902593176510#u64)
theorem pair0_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 382267175#u32 1444122533#u32 144389341#u32 63740878#u32)=ok raw0_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_0
def raw0_2_1 : Array U64 4#usize := (pack 2621525498612060639#u64 3269745139630906635#u64 7533125007782149900#u64 4150854274039461986#u64)
theorem pair0_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 382267175#u32 1444122533#u32 144389341#u32 63740878#u32)=ok raw0_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_1
theorem push0_2 : FIo_Native.fast_pairing.EbyKDot.push s0_2 JFw_TX2_P27.value
    JGw_Tails06.value2_0=ok (.Ok (),s0_3) := by
  have full : ¬s0_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value2_0=
      ok (.Ok (pack 382267175#u32 1444122533#u32 144389341#u32 63740878#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (382267175<2147483647 ∧ 1444122533<2147483647) ∧ (144389341<2147483647 ∧ 63740878<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 382267175#u32 1444122533#u32 144389341#u32 63740878#u32)=ok s0_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_2.c0 raw0_2_0=_
    simp only [s0_2,raw0_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 382267175#u32 1444122533#u32 144389341#u32 63740878#u32)=ok s0_3.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_2_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_2.c1 raw0_2_1=_
    simp only [s0_2,raw0_2_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s0_2.count 1#usize=s0_3.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s0_2.count (by unfold s0_2;decide)
  rw [inc]
#print axioms push0_2
def value0 : FIo_Install.NE := ⟨⟨⟨1880463181#u32,2018232740#u32⟩,⟨1496941575#u32,1931192415#u32⟩⟩,⟨⟨1094852464#u32,1665424325#u32⟩,⟨1554934735#u32,812667170#u32⟩⟩⟩
theorem finish0 : FIo_Native.fast_pairing.EbyKDot.finish s0_3=ok value0 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s0_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10470397769%2147483647 at h0
  norm_num at h0
  have e0 : a0=1880463181#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6313200034%2147483647 at h1
  norm_num at h1
  have e1 : a1=2018232740#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16529327104%2147483647 at h2
  norm_num at h2
  have e2 : a2=1496941575#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10521127003%2147483647 at h3
  norm_num at h3
  have e3 : a3=1931192415#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=7537303405%2147483647 at h4
  norm_num at h4
  have e4 : a4=1094852464#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=8107875266%2147483647 at h5
  norm_num at h5
  have e5 : a5=1665424325#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14439836617%2147483647 at h6
  norm_num at h6
  have e6 : a6=1554934735#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=9402601758%2147483647 at h7
  norm_num at h7
  have e7 : a7=812667170#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value0 := Subtype.ext h
  have same : out=value0 := JFw_TX2_CellUnique.source out value0 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish0
theorem source0 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨6,by decide⟩)
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok s0_0 from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JGw_Tails06.value0_0
      from JGw_Tails06.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JGw_Tails06.value1_0
      from JGw_Tails06.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JGw_Tails06.value2_0
      from JGw_Tails06.source2_0,
    push0_0,push0_1,push0_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish0]
#print axioms source0
def s1_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s1_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 2347974717#u64 1606803212#u64 3654539732#u64 2986898495#u64)⟩,⟨(pack 3603690210#u64 1376151263#u64 3347486075#u64 1849290035#u64)⟩,1#usize⟩
def raw1_0_0 : Array U64 4#usize := (pack 4228707523790928400#u64 2491566767157950848#u64 7182317882770614709#u64 5390602688350776084#u64)
theorem pair1_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 420016558#u32 880123152#u32 288524170#u32 1891289355#u32)=ok raw1_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_0
def raw1_0_1 : Array U64 4#usize := (pack 3704279350443210240#u64 916274513410777406#u64 6024810025485974499#u64 3887900371717241759#u64)
theorem pair1_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 420016558#u32 880123152#u32 288524170#u32 1891289355#u32)=ok raw1_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_1
theorem push1_0 : FIo_Native.fast_pairing.EbyKDot.push s1_0 JFw_TX2_P28.value
    JGw_Tails06.value0_1=ok (.Ok (),s1_1) := by
  have full : ¬s1_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value0_1=
      ok (.Ok (pack 420016558#u32 880123152#u32 288524170#u32 1891289355#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (420016558<2147483647 ∧ 880123152<2147483647) ∧ (288524170<2147483647 ∧ 1891289355<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 420016558#u32 880123152#u32 288524170#u32 1891289355#u32)=ok s1_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_0.c0 raw1_0_0=_
    simp only [s1_0,raw1_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 420016558#u32 880123152#u32 288524170#u32 1891289355#u32)=ok s1_1.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_0_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_0.c1 raw1_0_1=_
    simp only [s1_0,raw1_0_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s1_0.count 1#usize=s1_1.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s1_0.count (by unfold s1_0;decide)
  rw [inc]
#print axioms push1_0
def s1_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 5595599142#u64 3839063408#u64 8229600073#u64 5408324537#u64)⟩,⟨(pack 6523820431#u64 2070281653#u64 9457875958#u64 3120185789#u64)⟩,2#usize⟩
def raw1_1_0 : Array U64 4#usize := (pack 4580449104650355847#u64 511146916044450706#u64 9447527005126470130#u64 3692549011896984564#u64)
theorem pair1_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 33880487#u32 261649581#u32 577429976#u32 1596782335#u32)=ok raw1_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_0
def raw1_1_1 : Array U64 4#usize := (pack 4570811577819731162#u64 176826806370248896#u64 9079173296367713911#u64 1307636487947617184#u64)
theorem pair1_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 33880487#u32 261649581#u32 577429976#u32 1596782335#u32)=ok raw1_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_1
theorem push1_1 : FIo_Native.fast_pairing.EbyKDot.push s1_1 JFw_TX2_P26.value
    JGw_Tails06.value1_1=ok (.Ok (),s1_2) := by
  have full : ¬s1_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value1_1=
      ok (.Ok (pack 33880487#u32 261649581#u32 577429976#u32 1596782335#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (33880487<2147483647 ∧ 261649581<2147483647) ∧ (577429976<2147483647 ∧ 1596782335<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 33880487#u32 261649581#u32 577429976#u32 1596782335#u32)=ok s1_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_1.c0 raw1_1_0=_
    simp only [s1_1,raw1_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 33880487#u32 261649581#u32 577429976#u32 1596782335#u32)=ok s1_2.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_1_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_1.c1 raw1_1_1=_
    simp only [s1_1,raw1_1_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s1_1.count 1#usize=s1_2.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s1_1.count (by unfold s1_1;decide)
  rw [inc]
#print axioms push1_1
def s1_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 9756331717#u64 5927949985#u64 14285393908#u64 7592242680#u64)⟩,⟨(pack 11400143901#u64 6435619622#u64 16347176754#u64 9443375963#u64)⟩,3#usize⟩
def raw1_2_0 : Array U64 4#usize := (pack 5385159052555182687#u64 1486672380804624355#u64 10637079043334674075#u64 4020155162497058459#u64)
theorem pair1_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2136326315#u32 560193977#u32 1958984557#u32 1668239005#u32)=ok raw1_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_0
def raw1_2_1 : Array U64 4#usize := (pack 7368463158083761703#u64 4942204762751060826#u64 13136815292779049836#u64 11680880353742853128#u64)
theorem pair1_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2136326315#u32 560193977#u32 1958984557#u32 1668239005#u32)=ok raw1_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_1
theorem push1_2 : FIo_Native.fast_pairing.EbyKDot.push s1_2 JFw_TX2_P27.value
    JGw_Tails06.value2_1=ok (.Ok (),s1_3) := by
  have full : ¬s1_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value2_1=
      ok (.Ok (pack 2136326315#u32 560193977#u32 1958984557#u32 1668239005#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2136326315<2147483647 ∧ 560193977<2147483647) ∧ (1958984557<2147483647 ∧ 1668239005<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2136326315#u32 560193977#u32 1958984557#u32 1668239005#u32)=ok s1_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_2.c0 raw1_2_0=_
    simp only [s1_2,raw1_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2136326315#u32 560193977#u32 1958984557#u32 1668239005#u32)=ok s1_3.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_2_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_2.c1 raw1_2_1=_
    simp only [s1_2,raw1_2_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s1_2.count 1#usize=s1_3.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s1_2.count (by unfold s1_2;decide)
  rw [inc]
#print axioms push1_2
def value1 : FIo_Install.NE := ⟨⟨⟨1166397129#u32,1632982691#u32⟩,⟨1400492026#u32,1149791739#u32⟩⟩,⟨⟨662725666#u32,2140652328#u32⟩,⟨1314791225#u32,853441375#u32⟩⟩⟩
theorem finish1 : FIo_Native.fast_pairing.EbyKDot.finish s1_3=ok value1 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s1_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9756331717%2147483647 at h0
  norm_num at h0
  have e0 : a0=1166397129#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5927949985%2147483647 at h1
  norm_num at h1
  have e1 : a1=1632982691#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=14285393908%2147483647 at h2
  norm_num at h2
  have e2 : a2=1400492026#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=7592242680%2147483647 at h3
  norm_num at h3
  have e3 : a3=1149791739#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=11400143901%2147483647 at h4
  norm_num at h4
  have e4 : a4=662725666#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6435619622%2147483647 at h5
  norm_num at h5
  have e5 : a5=2140652328#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16347176754%2147483647 at h6
  norm_num at h6
  have e6 : a6=1314791225#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=9443375963%2147483647 at h7
  norm_num at h7
  have e7 : a7=853441375#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value1 := Subtype.ext h
  have same : out=value1 := JFw_TX2_CellUnique.source out value1 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish1
theorem source1 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨6,by decide⟩)
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok s1_0 from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JGw_Tails06.value0_1
      from JGw_Tails06.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JGw_Tails06.value1_1
      from JGw_Tails06.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JGw_Tails06.value2_1
      from JGw_Tails06.source2_1,
    push1_0,push1_1,push1_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish1]
#print axioms source1
def s2_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s2_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 3630813357#u64 2462866912#u64 6598985383#u64 3083295453#u64)⟩,⟨(pack 2835617032#u64 2450268635#u64 5445597449#u64 4143085027#u64)⟩,1#usize⟩
def raw2_0_0 : Array U64 4#usize := (pack 6403949861374985149#u64 4251083725834459552#u64 9937911323213916996#u64 2942202276936007706#u64)
theorem pair2_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1498697956#u32 969160313#u32 241188266#u32 576604325#u32)=ok raw2_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_0
def raw2_0_1 : Array U64 4#usize := (pack 4075874886250348494#u64 2298423641420913052#u64 9668248471907086212#u64 5674362277301825801#u64)
theorem pair2_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1498697956#u32 969160313#u32 241188266#u32 576604325#u32)=ok raw2_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_1
theorem push2_0 : FIo_Native.fast_pairing.EbyKDot.push s2_0 JFw_TX2_P28.value
    JGw_Tails06.value0_2=ok (.Ok (),s2_1) := by
  have full : ¬s2_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value0_2=
      ok (.Ok (pack 1498697956#u32 969160313#u32 241188266#u32 576604325#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1498697956<2147483647 ∧ 969160313<2147483647) ∧ (241188266<2147483647 ∧ 576604325<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1498697956#u32 969160313#u32 241188266#u32 576604325#u32)=ok s2_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_0.c0 raw2_0_0=_
    simp only [s2_0,raw2_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1498697956#u32 969160313#u32 241188266#u32 576604325#u32)=ok s2_1.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_0_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_0.c1 raw2_0_1=_
    simp only [s2_0,raw2_0_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s2_0.count 1#usize=s2_1.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s2_0.count (by unfold s2_0;decide)
  rw [inc]
#print axioms push2_0
def s2_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 7739163186#u64 5124611348#u64 13264987181#u64 7995143801#u64)⟩,⟨(pack 5959580389#u64 4633696394#u64 10611125840#u64 6986679966#u64)⟩,2#usize⟩
def raw2_1_0 : Array U64 4#usize := (pack 8171775541277391975#u64 2752071214792202964#u64 12319168543297251452#u64 7317865791253662536#u64)
theorem pair2_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2068724792#u32 1046353042#u32 982539638#u32 1404487134#u32)=ok raw2_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_0
def raw2_1_1 : Array U64 4#usize := (pack 5694729623223691526#u64 1170555235360779038#u64 9874341807214709290#u64 2802923410839165120#u64)
theorem pair2_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2068724792#u32 1046353042#u32 982539638#u32 1404487134#u32)=ok raw2_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_1
theorem push2_1 : FIo_Native.fast_pairing.EbyKDot.push s2_1 JFw_TX2_P26.value
    JGw_Tails06.value1_2=ok (.Ok (),s2_2) := by
  have full : ¬s2_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value1_2=
      ok (.Ok (pack 2068724792#u32 1046353042#u32 982539638#u32 1404487134#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2068724792<2147483647 ∧ 1046353042<2147483647) ∧ (982539638<2147483647 ∧ 1404487134<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2068724792#u32 1046353042#u32 982539638#u32 1404487134#u32)=ok s2_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_1.c0 raw2_1_0=_
    simp only [s2_1,raw2_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2068724792#u32 1046353042#u32 982539638#u32 1404487134#u32)=ok s2_2.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_1_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_1.c1 raw2_1_1=_
    simp only [s2_1,raw2_1_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s2_1.count 1#usize=s2_2.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s2_1.count (by unfold s2_1;decide)
  rw [inc]
#print axioms push2_1
def s2_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 10864481145#u64 7685048691#u64 19302929708#u64 11296020333#u64)⟩,⟨(pack 10461778868#u64 7382341942#u64 16289889738#u64 11317571496#u64)⟩,3#usize⟩
def raw2_2_0 : Array U64 4#usize := (pack 4888422504598224011#u64 1509579479817058124#u64 8887921971811267869#u64 3299000405860454957#u64)
theorem pair2_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1719132688#u32 1065574832#u32 245043575#u32 1935218702#u32)=ok raw2_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_0
def raw2_2_1 : Array U64 4#usize := (pack 5694015120285347749#u64 5068300555595059115#u64 7789313833508055080#u64 9299195814700738148#u64)
theorem pair2_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1719132688#u32 1065574832#u32 245043575#u32 1935218702#u32)=ok raw2_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_1
theorem push2_2 : FIo_Native.fast_pairing.EbyKDot.push s2_2 JFw_TX2_P27.value
    JGw_Tails06.value2_2=ok (.Ok (),s2_3) := by
  have full : ¬s2_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value2_2=
      ok (.Ok (pack 1719132688#u32 1065574832#u32 245043575#u32 1935218702#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1719132688<2147483647 ∧ 1065574832<2147483647) ∧ (245043575<2147483647 ∧ 1935218702<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1719132688#u32 1065574832#u32 245043575#u32 1935218702#u32)=ok s2_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_2.c0 raw2_2_0=_
    simp only [s2_2,raw2_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1719132688#u32 1065574832#u32 245043575#u32 1935218702#u32)=ok s2_3.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_2_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_2.c1 raw2_2_1=_
    simp only [s2_2,raw2_2_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s2_2.count 1#usize=s2_3.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s2_2.count (by unfold s2_2;decide)
  rw [inc]
#print axioms push2_2
def value2 : FIo_Install.NE := ⟨⟨⟨127062910#u32,1242597750#u32⟩,⟨2123060532#u32,558602098#u32⟩⟩,⟨⟨1871844280#u32,939891001#u32⟩,⟨1257504209#u32,580153261#u32⟩⟩⟩
theorem finish2 : FIo_Native.fast_pairing.EbyKDot.finish s2_3=ok value2 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s2_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10864481145%2147483647 at h0
  norm_num at h0
  have e0 : a0=127062910#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7685048691%2147483647 at h1
  norm_num at h1
  have e1 : a1=1242597750#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=19302929708%2147483647 at h2
  norm_num at h2
  have e2 : a2=2123060532#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=11296020333%2147483647 at h3
  norm_num at h3
  have e3 : a3=558602098#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10461778868%2147483647 at h4
  norm_num at h4
  have e4 : a4=1871844280#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7382341942%2147483647 at h5
  norm_num at h5
  have e5 : a5=939891001#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16289889738%2147483647 at h6
  norm_num at h6
  have e6 : a6=1257504209#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=11317571496%2147483647 at h7
  norm_num at h7
  have e7 : a7=580153261#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value2 := Subtype.ext h
  have same : out=value2 := JFw_TX2_CellUnique.source out value2 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish2
theorem source2 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨6,by decide⟩)
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok s2_0 from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JGw_Tails06.value0_2
      from JGw_Tails06.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JGw_Tails06.value1_2
      from JGw_Tails06.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JGw_Tails06.value2_2
      from JGw_Tails06.source2_2,
    push2_0,push2_1,push2_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish2]
#print axioms source2
def s3_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s3_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 2451268511#u64 3632372299#u64 6796910208#u64 3223707751#u64)⟩,⟨(pack 1460739244#u64 1689053520#u64 4100176839#u64 4772625956#u64)⟩,1#usize⟩
def raw3_0_0 : Array U64 4#usize := (pack 4844741943514852701#u64 5881637690457329065#u64 13400834197186017049#u64 6038136784889468307#u64)
theorem pair3_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1355120660#u32 1830051737#u32 1994193541#u32 490312958#u32)=ok raw3_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_0
def raw3_0_1 : Array U64 4#usize := (pack 2940356820209016518#u64 2504750998277821898#u64 8468712110196910640#u64 9284955900471339455#u64)
theorem pair3_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1355120660#u32 1830051737#u32 1994193541#u32 490312958#u32)=ok raw3_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_1
theorem push3_0 : FIo_Native.fast_pairing.EbyKDot.push s3_0 JFw_TX2_P28.value
    JGw_Tails06.value0_3=ok (.Ok (),s3_1) := by
  have full : ¬s3_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value0_3=
      ok (.Ok (pack 1355120660#u32 1830051737#u32 1994193541#u32 490312958#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1355120660<2147483647 ∧ 1830051737<2147483647) ∧ (1994193541<2147483647 ∧ 490312958<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1355120660#u32 1830051737#u32 1994193541#u32 490312958#u32)=ok s3_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_0.c0 raw3_0_0=_
    simp only [s3_0,raw3_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1355120660#u32 1830051737#u32 1994193541#u32 490312958#u32)=ok s3_1.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_0_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_0.c1 raw3_0_1=_
    simp only [s3_0,raw3_0_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s3_0.count 1#usize=s3_1.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s3_0.count (by unfold s3_0;decide)
  rw [inc]
#print axioms push3_0
def s3_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 4648787902#u64 5516212138#u64 13676120903#u64 4441536759#u64)⟩,⟨(pack 5403810215#u64 2776342316#u64 10583162328#u64 5710077621#u64)⟩,2#usize⟩
def raw3_1_0 : Array U64 4#usize := (pack 4577748662241501136#u64 649750724363705265#u64 11664163851964354133#u64 1506198237554960878#u64)
theorem pair3_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 45986829#u32 332038260#u32 1512030095#u32 206432454#u32)=ok raw3_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_0
def raw3_1_1 : Array U64 4#usize := (pack 4561744655924418507#u64 225113732480446046#u64 9980455256920103863#u64 674481709884368252#u64)
theorem pair3_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 45986829#u32 332038260#u32 1512030095#u32 206432454#u32)=ok raw3_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_1
theorem push3_1 : FIo_Native.fast_pairing.EbyKDot.push s3_1 JFw_TX2_P26.value
    JGw_Tails06.value1_3=ok (.Ok (),s3_2) := by
  have full : ¬s3_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value1_3=
      ok (.Ok (pack 45986829#u32 332038260#u32 1512030095#u32 206432454#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (45986829<2147483647 ∧ 332038260<2147483647) ∧ (1512030095<2147483647 ∧ 206432454<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 45986829#u32 332038260#u32 1512030095#u32 206432454#u32)=ok s3_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_1.c0 raw3_1_0=_
    simp only [s3_1,raw3_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 45986829#u32 332038260#u32 1512030095#u32 206432454#u32)=ok s3_2.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_1_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_1.c1 raw3_1_1=_
    simp only [s3_1,raw3_1_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s3_1.count 1#usize=s3_2.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s3_1.count (by unfold s3_1;decide)
  rw [inc]
#print axioms push3_1
def s3_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 8745856765#u64 8114759498#u64 18894008619#u64 7603146882#u64)⟩,⟨(pack 8056840375#u64 4865181453#u64 16149549462#u64 10334275870#u64)⟩,3#usize⟩
def raw3_2_0 : Array U64 4#usize := (pack 4845225163340966405#u64 1284625596407275336#u64 9070204145339922602#u64 2519753612566096493#u64)
theorem pair3_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1461218391#u32 908698346#u32 46953456#u32 1260044876#u32)=ok raw3_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_0
def raw3_2_1 : Array U64 4#usize := (pack 5526117463864941044#u64 4313226993056994735#u64 8423810449102441933#u64 6929207088066113573#u64)
theorem pair3_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1461218391#u32 908698346#u32 46953456#u32 1260044876#u32)=ok raw3_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_1
theorem push3_2 : FIo_Native.fast_pairing.EbyKDot.push s3_2 JFw_TX2_P27.value
    JGw_Tails06.value2_3=ok (.Ok (),s3_3) := by
  have full : ¬s3_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails06.value2_3=
      ok (.Ok (pack 1461218391#u32 908698346#u32 46953456#u32 1260044876#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1461218391<2147483647 ∧ 908698346<2147483647) ∧ (46953456<2147483647 ∧ 1260044876<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1461218391#u32 908698346#u32 46953456#u32 1260044876#u32)=ok s3_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_2.c0 raw3_2_0=_
    simp only [s3_2,raw3_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1461218391#u32 908698346#u32 46953456#u32 1260044876#u32)=ok s3_3.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_2_1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_2.c1 raw3_2_1=_
    simp only [s3_2,raw3_2_1,JFw_TX2_FoldPush.source]
    rfl
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_neg full,hw,r0,r1,checked,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift,d0,d1]
  have inc : Usize.wrapping_add s3_2.count 1#usize=s3_3.count := by
    apply UScalar.eq_of_val_eq
    exact Port3_Wrapping.increment s3_2.count (by unfold s3_2;decide)
  rw [inc]
#print axioms push3_2
def value3 : FIo_Install.NE := ⟨⟨⟨155922177#u32,1672308557#u32⟩,⟨1714139443#u32,1160695941#u32⟩⟩,⟨⟨1614389434#u32,570214159#u32⟩,⟨1117163933#u32,1744341282#u32⟩⟩⟩
theorem finish3 : FIo_Native.fast_pairing.EbyKDot.finish s3_3=ok value3 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s3_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=8745856765%2147483647 at h0
  norm_num at h0
  have e0 : a0=155922177#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=8114759498%2147483647 at h1
  norm_num at h1
  have e1 : a1=1672308557#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18894008619%2147483647 at h2
  norm_num at h2
  have e2 : a2=1714139443#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=7603146882%2147483647 at h3
  norm_num at h3
  have e3 : a3=1160695941#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8056840375%2147483647 at h4
  norm_num at h4
  have e4 : a4=1614389434#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=4865181453%2147483647 at h5
  norm_num at h5
  have e5 : a5=570214159#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16149549462%2147483647 at h6
  norm_num at h6
  have e6 : a6=1117163933#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10334275870%2147483647 at h7
  norm_num at h7
  have e7 : a7=1744341282#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value3 := Subtype.ext h
  have same : out=value3 := JFw_TX2_CellUnique.source out value3 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish3
theorem source3 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨6,by decide⟩)
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok s3_0 from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JGw_Tails06.value0_3
      from JGw_Tails06.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JGw_Tails06.value1_3
      from JGw_Tails06.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JGw_Tails06.value2_3
      from JGw_Tails06.source2_3,
    push3_0,push3_1,push3_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish3]
#print axioms source3
end AspisR1.JHa_Tails6
end
