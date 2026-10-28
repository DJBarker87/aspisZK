import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFw_TX2_CellUnique
import NDO_JGw_Tails03
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Tails3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def s0_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s0_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 3550106284#u64 1996049813#u64 7578573857#u64 4070957836#u64)⟩,⟨(pack 4455151418#u64 2360956264#u64 7376951372#u64 4345332752#u64)⟩,1#usize⟩
def raw0_0_0 : Array U64 4#usize := (pack 7594798847148034060#u64 2705398251219208917#u64 12194245314475100447#u64 4546493822044281591#u64)
theorem pair0_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1542961886#u32 215609565#u32 1366097767#u32 872916176#u32)=ok raw0_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_0
def raw0_0_1 : Array U64 4#usize := (pack 5033402498486353260#u64 2016512530150663804#u64 11465632128918036724#u64 5752169932919464937#u64)
theorem pair0_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1542961886#u32 215609565#u32 1366097767#u32 872916176#u32)=ok raw0_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_1
theorem push0_0 : FIo_Native.fast_pairing.EbyKDot.push s0_0 JFw_TX2_P28.value
    JGw_Tails03.value0_0=ok (.Ok (),s0_1) := by
  have full : ¬s0_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value0_0=
      ok (.Ok (pack 1542961886#u32 215609565#u32 1366097767#u32 872916176#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1542961886<2147483647 ∧ 215609565<2147483647) ∧ (1366097767<2147483647 ∧ 872916176<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1542961886#u32 215609565#u32 1366097767#u32 872916176#u32)=ok s0_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_0.c0 raw0_0_0=_
    simp only [s0_0,raw0_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1542961886#u32 215609565#u32 1366097767#u32 872916176#u32)=ok s0_1.c1 := by
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
def s0_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 8755045245#u64 4909549380#u64 13541682739#u64 9861889289#u64)⟩,⟨(pack 8518739150#u64 4861157531#u64 13063875733#u64 7008406834#u64)⟩,2#usize⟩
def raw0_1_0 : Array U64 4#usize := (pack 7449479534500992124#u64 4014415139154188054#u64 10917122335423791162#u64 9422729082810013091#u64)
theorem pair0_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1825984128#u32 1755241157#u32 1059342017#u32 2102109954#u32)=ok raw0_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_0
def raw0_1_1 : Array U64 4#usize := (pack 5368289413064650758#u64 1569442074623114419#u64 9240436819479122849#u64 3458586247960497510#u64)
theorem pair0_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1825984128#u32 1755241157#u32 1059342017#u32 2102109954#u32)=ok raw0_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_1
theorem push0_1 : FIo_Native.fast_pairing.EbyKDot.push s0_1 JFw_TX2_P26.value
    JGw_Tails03.value1_0=ok (.Ok (),s0_2) := by
  have full : ¬s0_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value1_0=
      ok (.Ok (pack 1825984128#u32 1755241157#u32 1059342017#u32 2102109954#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1825984128<2147483647 ∧ 1755241157<2147483647) ∧ (1059342017<2147483647 ∧ 2102109954<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1825984128#u32 1755241157#u32 1059342017#u32 2102109954#u32)=ok s0_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_1.c0 raw0_1_0=_
    simp only [s0_1,raw0_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1825984128#u32 1755241157#u32 1059342017#u32 2102109954#u32)=ok s0_2.c1 := by
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
def s0_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 13133097675#u64 6015525760#u64 20067011583#u64 11950818073#u64)⟩,⟨(pack 14151702985#u64 7794228497#u64 20897140699#u64 12245337649#u64)⟩,3#usize⟩
def raw0_2_0 : Array U64 4#usize := (pack 5445438349660626087#u64 1055030627790973620#u64 10777231733642217338#u64 3189632268699882180#u64)
theorem pair0_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1768128732#u32 119363658#u32 1877112031#u32 1389443863#u32)=ok raw0_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_0
def raw0_2_1 : Array U64 4#usize := (pack 7529548527131921408#u64 3479311282195209756#u64 13529990025883535050#u64 9423528352047105736#u64)
theorem pair0_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1768128732#u32 119363658#u32 1877112031#u32 1389443863#u32)=ok raw0_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_1
theorem push0_2 : FIo_Native.fast_pairing.EbyKDot.push s0_2 JFw_TX2_P27.value
    JGw_Tails03.value2_0=ok (.Ok (),s0_3) := by
  have full : ¬s0_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value2_0=
      ok (.Ok (pack 1768128732#u32 119363658#u32 1877112031#u32 1389443863#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1768128732<2147483647 ∧ 119363658<2147483647) ∧ (1877112031<2147483647 ∧ 1389443863<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1768128732#u32 119363658#u32 1877112031#u32 1389443863#u32)=ok s0_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_2.c0 raw0_2_0=_
    simp only [s0_2,raw0_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1768128732#u32 119363658#u32 1877112031#u32 1389443863#u32)=ok s0_3.c1 := by
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
def value0 : FIo_Install.NE := ⟨⟨⟨248195793#u32,1720558466#u32⟩,⟨739658760#u32,1213399838#u32⟩⟩,⟨⟨1266801103#u32,1351777556#u32⟩,⟨1569787876#u32,1507919414#u32⟩⟩⟩
theorem finish0 : FIo_Native.fast_pairing.EbyKDot.finish s0_3=ok value0 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s0_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=13133097675%2147483647 at h0
  norm_num at h0
  have e0 : a0=248195793#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6015525760%2147483647 at h1
  norm_num at h1
  have e1 : a1=1720558466#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=20067011583%2147483647 at h2
  norm_num at h2
  have e2 : a2=739658760#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=11950818073%2147483647 at h3
  norm_num at h3
  have e3 : a3=1213399838#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=14151702985%2147483647 at h4
  norm_num at h4
  have e4 : a4=1266801103#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7794228497%2147483647 at h5
  norm_num at h5
  have e5 : a5=1351777556#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=20897140699%2147483647 at h6
  norm_num at h6
  have e6 : a6=1569787876#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=12245337649%2147483647 at h7
  norm_num at h7
  have e7 : a7=1507919414#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value0 := Subtype.ext h
  have same : out=value0 := JFw_TX2_CellUnique.source out value0 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish0
theorem source0 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨3,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JGw_Tails03.value0_0
      from JGw_Tails03.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JGw_Tails03.value1_0
      from JGw_Tails03.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JGw_Tails03.value2_0
      from JGw_Tails03.source2_0,
    push0_0,push0_1,push0_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish0]
#print axioms source0
def s1_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s1_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 5327386075#u64 4465509239#u64 6490201611#u64 3903101470#u64)⟩,⟨(pack 3779006382#u64 3192130475#u64 6579149368#u64 5321497487#u64)⟩,1#usize⟩
def raw1_0_0 : Array U64 4#usize := (pack 6889676076651339285#u64 6225887727303044010#u64 13205969997447204494#u64 6276894000262452850#u64)
theorem pair1_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 2083990077#u32 1494895121#u32 1753391877#u32 797068343#u32)=ok raw1_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_0
def raw1_0_1 : Array U64 4#usize := (pack 3683388159401591719#u64 3261884782308160977#u64 10174799492675374531#u64 9955150717211640293#u64)
theorem pair1_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 2083990077#u32 1494895121#u32 1753391877#u32 797068343#u32)=ok raw1_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_1
theorem push1_0 : FIo_Native.fast_pairing.EbyKDot.push s1_0 JFw_TX2_P28.value
    JGw_Tails03.value0_1=ok (.Ok (),s1_1) := by
  have full : ¬s1_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value0_1=
      ok (.Ok (pack 2083990077#u32 1494895121#u32 1753391877#u32 797068343#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2083990077<2147483647 ∧ 1494895121<2147483647) ∧ (1753391877<2147483647 ∧ 797068343<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 2083990077#u32 1494895121#u32 1753391877#u32 797068343#u32)=ok s1_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_0.c0 raw1_0_0=_
    simp only [s1_0,raw1_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 2083990077#u32 1494895121#u32 1753391877#u32 797068343#u32)=ok s1_1.c1 := by
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
def s1_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 9316951243#u64 6789107155#u64 13562972168#u64 6437851262#u64)⟩,⟨(pack 8213621443#u64 4502842737#u64 12286151867#u64 8187149565#u64)⟩,2#usize⟩
def raw1_1_0 : Array U64 4#usize := (pack 6510702875848907622#u64 1547084413891680309#u64 12951615420629460680#u64 5310698442051186223#u64)
theorem pair1_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1111182333#u32 598153786#u32 1725532147#u32 1219805257#u32)=ok raw1_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_0
def raw1_1_1 : Array U64 4#usize := (pack 5184766740863311699#u64 652035586261443572#u64 10213149662793246592#u64 2109357345455898310#u64)
theorem pair1_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1111182333#u32 598153786#u32 1725532147#u32 1219805257#u32)=ok raw1_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_1
theorem push1_1 : FIo_Native.fast_pairing.EbyKDot.push s1_1 JFw_TX2_P26.value
    JGw_Tails03.value1_1=ok (.Ok (),s1_2) := by
  have full : ¬s1_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value1_1=
      ok (.Ok (pack 1111182333#u32 598153786#u32 1725532147#u32 1219805257#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1111182333<2147483647 ∧ 598153786<2147483647) ∧ (1725532147<2147483647 ∧ 1219805257<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1111182333#u32 598153786#u32 1725532147#u32 1219805257#u32)=ok s1_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_1.c0 raw1_1_0=_
    simp only [s1_1,raw1_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1111182333#u32 598153786#u32 1725532147#u32 1219805257#u32)=ok s1_2.c1 := by
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
def s1_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 12232643252#u64 8511693288#u64 18873932454#u64 8415531272#u64)⟩,⟨(pack 10845960628#u64 5575081262#u64 15615303632#u64 12933427832#u64)⟩,3#usize⟩
def raw1_2_0 : Array U64 4#usize := (pack 4336227795726183808#u64 431037765387673333#u64 8420168176995266030#u64 2559408211184013344#u64)
theorem pair1_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 177194841#u32 650438435#u32 1433142144#u32 2120506181#u32)=ok raw1_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_0
def raw1_2_1 : Array U64 4#usize := (pack 3724220852553130157#u64 1481983177446060043#u64 7035591929847345130#u64 8119917593558972780#u64)
theorem pair1_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 177194841#u32 650438435#u32 1433142144#u32 2120506181#u32)=ok raw1_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_1
theorem push1_2 : FIo_Native.fast_pairing.EbyKDot.push s1_2 JFw_TX2_P27.value
    JGw_Tails03.value2_1=ok (.Ok (),s1_3) := by
  have full : ¬s1_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value2_1=
      ok (.Ok (pack 177194841#u32 650438435#u32 1433142144#u32 2120506181#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (177194841<2147483647 ∧ 650438435<2147483647) ∧ (1433142144<2147483647 ∧ 2120506181<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 177194841#u32 650438435#u32 1433142144#u32 2120506181#u32)=ok s1_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_2.c0 raw1_2_0=_
    simp only [s1_2,raw1_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 177194841#u32 650438435#u32 1433142144#u32 2120506181#u32)=ok s1_3.c1 := by
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
def value1 : FIo_Install.NE := ⟨⟨⟨1495225017#u32,2069242347#u32⟩,⟨1694063278#u32,1973080331#u32⟩⟩,⟨⟨108542393#u32,1280113968#u32⟩,⟨582918103#u32,48525950#u32⟩⟩⟩
theorem finish1 : FIo_Native.fast_pairing.EbyKDot.finish s1_3=ok value1 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s1_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=12232643252%2147483647 at h0
  norm_num at h0
  have e0 : a0=1495225017#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=8511693288%2147483647 at h1
  norm_num at h1
  have e1 : a1=2069242347#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18873932454%2147483647 at h2
  norm_num at h2
  have e2 : a2=1694063278#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8415531272%2147483647 at h3
  norm_num at h3
  have e3 : a3=1973080331#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10845960628%2147483647 at h4
  norm_num at h4
  have e4 : a4=108542393#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5575081262%2147483647 at h5
  norm_num at h5
  have e5 : a5=1280113968#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15615303632%2147483647 at h6
  norm_num at h6
  have e6 : a6=582918103#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=12933427832%2147483647 at h7
  norm_num at h7
  have e7 : a7=48525950#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value1 := Subtype.ext h
  have same : out=value1 := JFw_TX2_CellUnique.source out value1 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish1
theorem source1 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨3,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JGw_Tails03.value0_1
      from JGw_Tails03.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JGw_Tails03.value1_1
      from JGw_Tails03.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JGw_Tails03.value2_1
      from JGw_Tails03.source2_1,
    push1_0,push1_1,push1_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish1]
#print axioms source1
def s2_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s2_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 2815567188#u64 4446881676#u64 6219608397#u64 4939981481#u64)⟩,⟨(pack 3393512548#u64 2417701583#u64 5387563778#u64 5885581684#u64)⟩,1#usize⟩
def raw2_0_0 : Array U64 4#usize := (pack 5637322024911802445#u64 6336105027659189157#u64 10926048400851170058#u64 6275943187882238082#u64)
theorem pair2_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1707517246#u32 1802811910#u32 1130649608#u32 1147689682#u32)=ok raw2_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_0
def raw2_0_1 : Array U64 4#usize := (pack 3131849154420524024#u64 2931097928242069181#u64 8044720501510538666#u64 9183640378340354284#u64)
theorem pair2_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1707517246#u32 1802811910#u32 1130649608#u32 1147689682#u32)=ok raw2_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_1
theorem push2_0 : FIo_Native.fast_pairing.EbyKDot.push s2_0 JFw_TX2_P28.value
    JGw_Tails03.value0_2=ok (.Ok (),s2_1) := by
  have full : ¬s2_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value0_2=
      ok (.Ok (pack 1707517246#u32 1802811910#u32 1130649608#u32 1147689682#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1707517246<2147483647 ∧ 1802811910<2147483647) ∧ (1130649608<2147483647 ∧ 1147689682<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1707517246#u32 1802811910#u32 1130649608#u32 1147689682#u32)=ok s2_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_0.c0 raw2_0_0=_
    simp only [s2_0,raw2_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1707517246#u32 1802811910#u32 1130649608#u32 1147689682#u32)=ok s2_1.c1 := by
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
def s2_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 5624217258#u64 4650260774#u64 11097741314#u64 7697242003#u64)⟩,⟨(pack 5653760371#u64 3114508908#u64 11568332678#u64 7201772794#u64)⟩,2#usize⟩
def raw2_1_0 : Array U64 4#usize := (pack 5052356831753368012#u64 99218827788571547#u64 10388314371132292338#u64 2878207906026983228#u64)
theorem pair2_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 232600410#u32 7365204#u32 666585499#u32 1216299025#u32)=ok raw2_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_0
def raw2_1_1 : Array U64 4#usize := (pack 4759895656852327756#u64 60505328828712208#u64 9464369171219786057#u64 1080163099420948043#u64)
theorem pair2_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 232600410#u32 7365204#u32 666585499#u32 1216299025#u32)=ok raw2_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_1
theorem push2_1 : FIo_Native.fast_pairing.EbyKDot.push s2_1 JFw_TX2_P26.value
    JGw_Tails03.value1_2=ok (.Ok (),s2_2) := by
  have full : ¬s2_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value1_2=
      ok (.Ok (pack 232600410#u32 7365204#u32 666585499#u32 1216299025#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (232600410<2147483647 ∧ 7365204<2147483647) ∧ (666585499<2147483647 ∧ 1216299025<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 232600410#u32 7365204#u32 666585499#u32 1216299025#u32)=ok s2_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_1.c0 raw2_1_0=_
    simp only [s2_1,raw2_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 232600410#u32 7365204#u32 666585499#u32 1216299025#u32)=ok s2_2.c1 := by
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
def s2_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 9952523019#u64 5527255791#u64 16417042852#u64 9463223479#u64)⟩,⟨(pack 9217128114#u64 5479316970#u64 17638097184#u64 10204392450#u64)⟩,3#usize⟩
def raw2_2_0 : Array U64 4#usize := (pack 4872157505461023106#u64 997839023463714605#u64 10250046422905725902#u64 2041131971427147703#u64)
theorem pair2_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1204976718#u32 628617535#u32 1040833513#u32 57775562#u32)=ok raw2_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_0
def raw2_2_1 : Array U64 4#usize := (pack 5588865998490264888#u64 3342555741267284485#u64 12377059550010865007#u64 5567348473779581735#u64)
theorem pair2_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1204976718#u32 628617535#u32 1040833513#u32 57775562#u32)=ok raw2_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_1
theorem push2_2 : FIo_Native.fast_pairing.EbyKDot.push s2_2 JFw_TX2_P27.value
    JGw_Tails03.value2_2=ok (.Ok (),s2_3) := by
  have full : ¬s2_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value2_2=
      ok (.Ok (pack 1204976718#u32 628617535#u32 1040833513#u32 57775562#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1204976718<2147483647 ∧ 628617535<2147483647) ∧ (1040833513<2147483647 ∧ 57775562<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1204976718#u32 628617535#u32 1040833513#u32 57775562#u32)=ok s2_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_2.c0 raw2_2_0=_
    simp only [s2_2,raw2_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1204976718#u32 628617535#u32 1040833513#u32 57775562#u32)=ok s2_3.c1 := by
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
def value2 : FIo_Install.NE := ⟨⟨⟨1362588431#u32,1232288497#u32⟩,⟨1384657323#u32,873288891#u32⟩⟩,⟨⟨627193526#u32,1184349676#u32⟩,⟨458228008#u32,1614457862#u32⟩⟩⟩
theorem finish2 : FIo_Native.fast_pairing.EbyKDot.finish s2_3=ok value2 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s2_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9952523019%2147483647 at h0
  norm_num at h0
  have e0 : a0=1362588431#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5527255791%2147483647 at h1
  norm_num at h1
  have e1 : a1=1232288497#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16417042852%2147483647 at h2
  norm_num at h2
  have e2 : a2=1384657323#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9463223479%2147483647 at h3
  norm_num at h3
  have e3 : a3=873288891#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9217128114%2147483647 at h4
  norm_num at h4
  have e4 : a4=627193526#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5479316970%2147483647 at h5
  norm_num at h5
  have e5 : a5=1184349676#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=17638097184%2147483647 at h6
  norm_num at h6
  have e6 : a6=458228008#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10204392450%2147483647 at h7
  norm_num at h7
  have e7 : a7=1614457862#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value2 := Subtype.ext h
  have same : out=value2 := JFw_TX2_CellUnique.source out value2 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish2
theorem source2 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨3,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JGw_Tails03.value0_2
      from JGw_Tails03.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JGw_Tails03.value1_2
      from JGw_Tails03.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JGw_Tails03.value2_2
      from JGw_Tails03.source2_2,
    push2_0,push2_1,push2_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish2]
#print axioms source2
def s3_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s3_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 4402733394#u64 3027930366#u64 6961720680#u64 1665961087#u64)⟩,⟨(pack 3723204490#u64 2247484914#u64 6208979818#u64 3380986135#u64)⟩,1#usize⟩
def raw3_0_0 : Array U64 4#usize := (pack 5157555524568727162#u64 3376184934262984800#u64 11876845119855222269#u64 2668437731599460490#u64)
theorem pair3_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 909643824#u32 960765051#u32 1013799738#u32 15210828#u32)=ok raw3_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_0
def raw3_0_1 : Array U64 4#usize := (pack 3822892352072077021#u64 1561639407287388266#u64 9520660399877596937#u64 5138536495688597928#u64)
theorem pair3_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 909643824#u32 960765051#u32 1013799738#u32 15210828#u32)=ok raw3_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_1
theorem push3_0 : FIo_Native.fast_pairing.EbyKDot.push s3_0 JFw_TX2_P28.value
    JGw_Tails03.value0_3=ok (.Ok (),s3_1) := by
  have full : ¬s3_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value0_3=
      ok (.Ok (pack 909643824#u32 960765051#u32 1013799738#u32 15210828#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (909643824<2147483647 ∧ 960765051<2147483647) ∧ (1013799738<2147483647 ∧ 15210828<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 909643824#u32 960765051#u32 1013799738#u32 15210828#u32)=ok s3_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_0.c0 raw3_0_0=_
    simp only [s3_0,raw3_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 909643824#u32 960765051#u32 1013799738#u32 15210828#u32)=ok s3_1.c1 := by
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
def s3_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 8776268688#u64 5958428090#u64 12613792633#u64 6335044334#u64)⟩,⟨(pack 7767866485#u64 4273573666#u64 11194821619#u64 6420829782#u64)⟩,2#usize⟩
def raw3_1_0 : Array U64 4#usize := (pack 5544360148040666595#u64 2299163943938772451#u64 10757341404222997515#u64 6149975932931823970#u64)
theorem pair3_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 695368017#u32 1072597060#u32 1310955724#u32 1651541099#u32)=ok raw3_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_0
def raw3_1_1 : Array U64 4#usize := (pack 4802931355476673454#u64 858270725204690902#u64 9380365919061173844#u64 2269210015358558279#u64)
theorem pair3_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 695368017#u32 1072597060#u32 1310955724#u32 1651541099#u32)=ok raw3_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_1
theorem push3_1 : FIo_Native.fast_pairing.EbyKDot.push s3_1 JFw_TX2_P26.value
    JGw_Tails03.value1_3=ok (.Ok (),s3_2) := by
  have full : ¬s3_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value1_3=
      ok (.Ok (pack 695368017#u32 1072597060#u32 1310955724#u32 1651541099#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (695368017<2147483647 ∧ 1072597060<2147483647) ∧ (1310955724<2147483647 ∧ 1651541099<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 695368017#u32 1072597060#u32 1310955724#u32 1651541099#u32)=ok s3_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_1.c0 raw3_1_0=_
    simp only [s3_1,raw3_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 695368017#u32 1072597060#u32 1310955724#u32 1651541099#u32)=ok s3_2.c1 := by
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
def s3_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 10979496705#u64 6717308293#u64 18525979926#u64 9730970612#u64)⟩,⟨(pack 10950644527#u64 7997563494#u64 16054550115#u64 11898805334#u64)⟩,3#usize⟩
def raw3_2_0 : Array U64 4#usize := (pack 4189350002437093422#u64 1460880697147222345#u64 9270416720061172694#u64 3889373804743757642#u64)
theorem pair3_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1052961069#u32 1705191509#u32 2043996202#u32 1047418933#u32)=ok raw3_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_0
def raw3_2_1 : Array U64 4#usize := (pack 3329566107425790275#u64 4972563396977451812#u64 10036087756202631464#u64 11189517136478402790#u64)
theorem pair3_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1052961069#u32 1705191509#u32 2043996202#u32 1047418933#u32)=ok raw3_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_1
theorem push3_2 : FIo_Native.fast_pairing.EbyKDot.push s3_2 JFw_TX2_P27.value
    JGw_Tails03.value2_3=ok (.Ok (),s3_3) := by
  have full : ¬s3_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails03.value2_3=
      ok (.Ok (pack 1052961069#u32 1705191509#u32 2043996202#u32 1047418933#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1052961069<2147483647 ∧ 1705191509<2147483647) ∧ (2043996202<2147483647 ∧ 1047418933<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1052961069#u32 1705191509#u32 2043996202#u32 1047418933#u32)=ok s3_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_2.c0 raw3_2_0=_
    simp only [s3_2,raw3_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1052961069#u32 1705191509#u32 2043996202#u32 1047418933#u32)=ok s3_3.c1 := by
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
def value3 : FIo_Install.NE := ⟨⟨⟨242078470#u32,274857352#u32⟩,⟨1346110750#u32,1141036024#u32⟩⟩,⟨⟨213226292#u32,1555112553#u32⟩,⟨1022164586#u32,1161387099#u32⟩⟩⟩
theorem finish3 : FIo_Native.fast_pairing.EbyKDot.finish s3_3=ok value3 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s3_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10979496705%2147483647 at h0
  norm_num at h0
  have e0 : a0=242078470#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6717308293%2147483647 at h1
  norm_num at h1
  have e1 : a1=274857352#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18525979926%2147483647 at h2
  norm_num at h2
  have e2 : a2=1346110750#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9730970612%2147483647 at h3
  norm_num at h3
  have e3 : a3=1141036024#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10950644527%2147483647 at h4
  norm_num at h4
  have e4 : a4=213226292#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7997563494%2147483647 at h5
  norm_num at h5
  have e5 : a5=1555112553#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16054550115%2147483647 at h6
  norm_num at h6
  have e6 : a6=1022164586#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=11898805334%2147483647 at h7
  norm_num at h7
  have e7 : a7=1161387099#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value3 := Subtype.ext h
  have same : out=value3 := JFw_TX2_CellUnique.source out value3 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish3
theorem source3 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨3,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JGw_Tails03.value0_3
      from JGw_Tails03.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JGw_Tails03.value1_3
      from JGw_Tails03.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨3,by decide⟩)
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JGw_Tails03.value2_3
      from JGw_Tails03.source2_3,
    push3_0,push3_1,push3_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish3]
#print axioms source3
end AspisR1.JHa_Tails3
end
