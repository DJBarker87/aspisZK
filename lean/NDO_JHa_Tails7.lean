import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFw_TX2_CellUnique
import NDO_JGw_Tails07
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Tails7
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def s0_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s0_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 3308213259#u64 984637507#u64 4243286139#u64 2288516261#u64)⟩,⟨(pack 2534982738#u64 516289310#u64 3355773531#u64 1337196946#u64)⟩,1#usize⟩
def raw0_0_0 : Array U64 4#usize := (pack 3974968162761014036#u64 954698860241933607#u64 7098220433025500347#u64 4601541037384536642#u64)
theorem pair0_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 4258606#u32 443918932#u32 279560532#u32 1775225813#u32)=ok raw0_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_0
def raw0_0_1 : Array U64 4#usize := (pack 4061169611572276181#u64 203823617687794206#u64 6221833816086167699#u64 2061962317561127415#u64)
theorem pair0_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 4258606#u32 443918932#u32 279560532#u32 1775225813#u32)=ok raw0_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_1
theorem push0_0 : FIo_Native.fast_pairing.EbyKDot.push s0_0 JFw_TX2_P28.value
    JGw_Tails07.value0_0=ok (.Ok (),s0_1) := by
  have full : ¬s0_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value0_0=
      ok (.Ok (pack 4258606#u32 443918932#u32 279560532#u32 1775225813#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (4258606<2147483647 ∧ 443918932<2147483647) ∧ (279560532<2147483647 ∧ 1775225813<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 4258606#u32 443918932#u32 279560532#u32 1775225813#u32)=ok s0_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_0.c0 raw0_0_0=_
    simp only [s0_0,raw0_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 4258606#u32 443918932#u32 279560532#u32 1775225813#u32)=ok s0_1.c1 := by
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
def s0_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 6482447394#u64 3738987432#u64 8358021268#u64 7469535113#u64)⟩,⟨(pack 6068760266#u64 2188226270#u64 8978198396#u64 3509784409#u64)⟩,2#usize⟩
def raw0_1_0 : Array U64 4#usize := (pack 6015304156737022354#u64 3657435623081928385#u64 8379379036764163692#u64 6645703775084053030#u64)
theorem pair0_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1065668039#u32 1714033729#u32 158789178#u32 1373067199#u32)=ok raw0_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_0
def raw0_1_1 : Array U64 4#usize := (pack 4887933720548757204#u64 1360617886332483132#u64 8508430266299538595#u64 2319770792530548554#u64)
theorem pair0_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1065668039#u32 1714033729#u32 158789178#u32 1373067199#u32)=ok raw0_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_1
theorem push0_1 : FIo_Native.fast_pairing.EbyKDot.push s0_1 JFw_TX2_P26.value
    JGw_Tails07.value1_0=ok (.Ok (),s0_2) := by
  have full : ¬s0_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value1_0=
      ok (.Ok (pack 1065668039#u32 1714033729#u32 158789178#u32 1373067199#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1065668039<2147483647 ∧ 1714033729<2147483647) ∧ (158789178<2147483647 ∧ 1373067199<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1065668039#u32 1714033729#u32 158789178#u32 1373067199#u32)=ok s0_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_1.c0 raw0_1_0=_
    simp only [s0_1,raw0_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1065668039#u32 1714033729#u32 158789178#u32 1373067199#u32)=ok s0_2.c1 := by
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
def s0_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 9499338031#u64 5451328232#u64 14005273622#u64 10928369110#u64)⟩,⟨(pack 9869999804#u64 5316183033#u64 15699432443#u64 10273287472#u64)⟩,3#usize⟩
def raw0_2_0 : Array U64 4#usize := (pack 4927775183123260982#u64 1547577237155089576#u64 10437677266382492458#u64 3935992124992566870#u64)
theorem pair0_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1791064466#u32 1060767618#u32 2133632685#u32 1003031405#u32)=ok raw0_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_0
def raw0_2_1 : Array U64 4#usize := (pack 5830578153067483154#u64 5192695116037391287#u64 13026013518054457328#u64 11255966524537072130#u64)
theorem pair0_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1791064466#u32 1060767618#u32 2133632685#u32 1003031405#u32)=ok raw0_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_1
theorem push0_2 : FIo_Native.fast_pairing.EbyKDot.push s0_2 JFw_TX2_P27.value
    JGw_Tails07.value2_0=ok (.Ok (),s0_3) := by
  have full : ¬s0_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value2_0=
      ok (.Ok (pack 1791064466#u32 1060767618#u32 2133632685#u32 1003031405#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1791064466<2147483647 ∧ 1060767618<2147483647) ∧ (2133632685<2147483647 ∧ 1003031405<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1791064466#u32 1060767618#u32 2133632685#u32 1003031405#u32)=ok s0_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_2.c0 raw0_2_0=_
    simp only [s0_2,raw0_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1791064466#u32 1060767618#u32 2133632685#u32 1003031405#u32)=ok s0_3.c1 := by
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
def value0 : FIo_Install.NE := ⟨⟨⟨909403443#u32,1156360938#u32⟩,⟨1120371740#u32,190950875#u32⟩⟩,⟨⟨1280065216#u32,1021215739#u32⟩,⟨667046914#u32,1683352884#u32⟩⟩⟩
theorem finish0 : FIo_Native.fast_pairing.EbyKDot.finish s0_3=ok value0 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s0_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9499338031%2147483647 at h0
  norm_num at h0
  have e0 : a0=909403443#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5451328232%2147483647 at h1
  norm_num at h1
  have e1 : a1=1156360938#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=14005273622%2147483647 at h2
  norm_num at h2
  have e2 : a2=1120371740#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10928369110%2147483647 at h3
  norm_num at h3
  have e3 : a3=190950875#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9869999804%2147483647 at h4
  norm_num at h4
  have e4 : a4=1280065216#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5316183033%2147483647 at h5
  norm_num at h5
  have e5 : a5=1021215739#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15699432443%2147483647 at h6
  norm_num at h6
  have e6 : a6=667046914#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10273287472%2147483647 at h7
  norm_num at h7
  have e7 : a7=1683352884#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value0 := Subtype.ext h
  have same : out=value0 := JFw_TX2_CellUnique.source out value0 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish0
theorem source0 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨7,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JGw_Tails07.value0_0
      from JGw_Tails07.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JGw_Tails07.value1_0
      from JGw_Tails07.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JGw_Tails07.value2_0
      from JGw_Tails07.source2_0,
    push0_0,push0_1,push0_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish0]
#print axioms source0
def s1_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s1_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 4842186466#u64 2976614863#u64 6207044095#u64 3444406631#u64)⟩,⟨(pack 3074065754#u64 2951884278#u64 5883767911#u64 4276516857#u64)⟩,1#usize⟩
def raw1_0_0 : Array U64 4#usize := (pack 7135245931474251301#u64 4314760125470036701#u64 12288961846733547166#u64 6985885758073062716#u64)
theorem pair1_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1746411499#u32 830298955#u32 1797403765#u32 1430623501#u32)=ok raw1_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_0
def raw1_0_1 : Array U64 4#usize := (pack 4359456005507692819#u64 2544583022293931113#u64 10099674052229639251#u64 8224632204989231397#u64)
theorem pair1_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1746411499#u32 830298955#u32 1797403765#u32 1430623501#u32)=ok raw1_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_1
theorem push1_0 : FIo_Native.fast_pairing.EbyKDot.push s1_0 JFw_TX2_P28.value
    JGw_Tails07.value0_1=ok (.Ok (),s1_1) := by
  have full : ¬s1_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value0_1=
      ok (.Ok (pack 1746411499#u32 830298955#u32 1797403765#u32 1430623501#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1746411499<2147483647 ∧ 830298955<2147483647) ∧ (1797403765<2147483647 ∧ 1430623501<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1746411499#u32 830298955#u32 1797403765#u32 1430623501#u32)=ok s1_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_0.c0 raw1_0_0=_
    simp only [s1_0,raw1_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1746411499#u32 830298955#u32 1797403765#u32 1430623501#u32)=ok s1_1.c1 := by
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
def s1_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 8161318733#u64 6595524445#u64 11998178300#u64 7750497422#u64)⟩,⟨(pack 6225330549#u64 3687819557#u64 11071661122#u64 7288511199#u64)⟩,2#usize⟩
def raw1_1_0 : Array U64 4#usize := (pack 5661508163068920080#u64 4342992786529278899#u64 8027010781950401136#u64 6586544390042911924#u64)
theorem pair1_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 953303807#u32 2095279187#u32 271395254#u32 1097149181#u32)=ok raw1_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_0
def raw1_1_1 : Array U64 4#usize := (pack 4724095995098809229#u64 1579501043027702662#u64 8377921933675610275#u64 2280043765387146100#u64)
theorem pair1_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 953303807#u32 2095279187#u32 271395254#u32 1097149181#u32)=ok raw1_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_1
theorem push1_1 : FIo_Native.fast_pairing.EbyKDot.push s1_1 JFw_TX2_P26.value
    JGw_Tails07.value1_1=ok (.Ok (),s1_2) := by
  have full : ¬s1_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value1_1=
      ok (.Ok (pack 953303807#u32 2095279187#u32 271395254#u32 1097149181#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (953303807<2147483647 ∧ 2095279187<2147483647) ∧ (271395254<2147483647 ∧ 1097149181<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 953303807#u32 2095279187#u32 271395254#u32 1097149181#u32)=ok s1_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_1.c0 raw1_1_0=_
    simp only [s1_1,raw1_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 953303807#u32 2095279187#u32 271395254#u32 1097149181#u32)=ok s1_2.c1 := by
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
def s1_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 12477431010#u64 8647854743#u64 18001531628#u64 11317781367#u64)⟩,⟨(pack 9661670126#u64 7198607058#u64 18861787721#u64 13811088962#u64)⟩,3#usize⟩
def raw1_2_0 : Array U64 4#usize := (pack 4707346693263912917#u64 1583361068890168889#u64 10103494485886779784#u64 3855122190217258112#u64)
theorem pair1_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1630952525#u32 1307702189#u32 1957698196#u32 871856145#u32)=ok raw1_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_0
def raw1_2_1 : Array U64 4#usize := (pack 5090051784635540279#u64 5335124667205027441#u64 12163853544146240852#u64 10930325866456416374#u64)
theorem pair1_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1630952525#u32 1307702189#u32 1957698196#u32 871856145#u32)=ok raw1_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_1
theorem push1_2 : FIo_Native.fast_pairing.EbyKDot.push s1_2 JFw_TX2_P27.value
    JGw_Tails07.value2_1=ok (.Ok (),s1_3) := by
  have full : ¬s1_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value2_1=
      ok (.Ok (pack 1630952525#u32 1307702189#u32 1957698196#u32 871856145#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1630952525<2147483647 ∧ 1307702189<2147483647) ∧ (1957698196<2147483647 ∧ 871856145<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1630952525#u32 1307702189#u32 1957698196#u32 871856145#u32)=ok s1_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_2.c0 raw1_2_0=_
    simp only [s1_2,raw1_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1630952525#u32 1307702189#u32 1957698196#u32 871856145#u32)=ok s1_3.c1 := by
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
def value1 : FIo_Install.NE := ⟨⟨⟨1740012775#u32,57920155#u32⟩,⟨821662452#u32,580363132#u32⟩⟩,⟨⟨1071735538#u32,756156117#u32⟩,⟨1681918545#u32,926187080#u32⟩⟩⟩
theorem finish1 : FIo_Native.fast_pairing.EbyKDot.finish s1_3=ok value1 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s1_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=12477431010%2147483647 at h0
  norm_num at h0
  have e0 : a0=1740012775#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=8647854743%2147483647 at h1
  norm_num at h1
  have e1 : a1=57920155#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18001531628%2147483647 at h2
  norm_num at h2
  have e2 : a2=821662452#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=11317781367%2147483647 at h3
  norm_num at h3
  have e3 : a3=580363132#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9661670126%2147483647 at h4
  norm_num at h4
  have e4 : a4=1071735538#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7198607058%2147483647 at h5
  norm_num at h5
  have e5 : a5=756156117#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=18861787721%2147483647 at h6
  norm_num at h6
  have e6 : a6=1681918545#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=13811088962%2147483647 at h7
  norm_num at h7
  have e7 : a7=926187080#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value1 := Subtype.ext h
  have same : out=value1 := JFw_TX2_CellUnique.source out value1 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish1
theorem source1 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨7,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JGw_Tails07.value0_1
      from JGw_Tails07.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JGw_Tails07.value1_1
      from JGw_Tails07.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JGw_Tails07.value2_1
      from JGw_Tails07.source2_1,
    push1_0,push1_1,push1_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish1]
#print axioms source1
def s2_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s2_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 3222445502#u64 3867499986#u64 4884986951#u64 3785856908#u64)⟩,⟨(pack 2493578798#u64 2416216492#u64 2520573490#u64 4346950542#u64)⟩,1#usize⟩
def raw2_0_0 : Array U64 4#usize := (pack 3174635798820911326#u64 4687209240441175522#u64 7976443710877921713#u64 6569873085276476934#u64)
theorem pair2_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 561004075#u32 1811733014#u32 662106175#u32 1774215201#u32)=ok raw2_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_0
def raw2_0_1 : Array U64 4#usize := (pack 2608017637921122748#u64 1508345411015219547#u64 4683310645741877698#u64 6507028203121278005#u64)
theorem pair2_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 561004075#u32 1811733014#u32 662106175#u32 1774215201#u32)=ok raw2_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_1
theorem push2_0 : FIo_Native.fast_pairing.EbyKDot.push s2_0 JFw_TX2_P28.value
    JGw_Tails07.value0_2=ok (.Ok (),s2_1) := by
  have full : ¬s2_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value0_2=
      ok (.Ok (pack 561004075#u32 1811733014#u32 662106175#u32 1774215201#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (561004075<2147483647 ∧ 1811733014<2147483647) ∧ (662106175<2147483647 ∧ 1774215201<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 561004075#u32 1811733014#u32 662106175#u32 1774215201#u32)=ok s2_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_0.c0 raw2_0_0=_
    simp only [s2_0,raw2_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 561004075#u32 1811733014#u32 662106175#u32 1774215201#u32)=ok s2_1.c1 := by
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
def s2_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 7952372836#u64 7258640506#u64 10385810929#u64 8676316215#u64)⟩,⟨(pack 5820499438#u64 3480381448#u64 7241401919#u64 7164738341#u64)⟩,2#usize⟩
def raw2_1_0 : Array U64 4#usize := (pack 6336059381029834183#u64 4523767998360675483#u64 11518574745766036546#u64 6577815430095457307#u64)
theorem pair2_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1312162798#u32 2121173865#u32 1732052852#u32 544996707#u32)=ok raw2_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_0
def raw2_1_1 : Array U64 4#usize := (pack 4949272433190114724#u64 1682219049515023292#u64 9602315715287552388#u64 2490877043866159269#u64)
theorem pair2_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1312162798#u32 2121173865#u32 1732052852#u32 544996707#u32)=ok raw2_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_1
theorem push2_1 : FIo_Native.fast_pairing.EbyKDot.push s2_1 JFw_TX2_P26.value
    JGw_Tails07.value1_2=ok (.Ok (),s2_2) := by
  have full : ¬s2_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value1_2=
      ok (.Ok (pack 1312162798#u32 2121173865#u32 1732052852#u32 544996707#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1312162798<2147483647 ∧ 2121173865<2147483647) ∧ (1732052852<2147483647 ∧ 544996707<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1312162798#u32 2121173865#u32 1732052852#u32 544996707#u32)=ok s2_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_1.c0 raw2_1_0=_
    simp only [s2_1,raw2_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1312162798#u32 2121173865#u32 1732052852#u32 544996707#u32)=ok s2_2.c1 := by
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
def s2_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 11003391596#u64 8906796290#u64 15619679608#u64 10262063829#u64)⟩,⟨(pack 9837761067#u64 5600540733#u64 12948641796#u64 11955254043#u64)⟩,3#usize⟩
def raw2_2_0 : Array U64 4#usize := (pack 4748587092509858926#u64 1165494483452921451#u64 8844139671412611887#u64 2454455606164365793#u64)
theorem pair2_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1259360088#u32 897654868#u32 81058558#u32 1409606157#u32)=ok raw2_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_0
def raw2_2_1 : Array U64 4#usize := (pack 5188225353053764941#u64 3920597676676975252#u64 7798822051459341082#u64 6864944954355947990#u64)
theorem pair2_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1259360088#u32 897654868#u32 81058558#u32 1409606157#u32)=ok raw2_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_1
theorem push2_2 : FIo_Native.fast_pairing.EbyKDot.push s2_2 JFw_TX2_P27.value
    JGw_Tails07.value2_2=ok (.Ok (),s2_3) := by
  have full : ¬s2_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value2_2=
      ok (.Ok (pack 1259360088#u32 897654868#u32 81058558#u32 1409606157#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1259360088<2147483647 ∧ 897654868<2147483647) ∧ (81058558<2147483647 ∧ 1409606157<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1259360088#u32 897654868#u32 81058558#u32 1409606157#u32)=ok s2_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_2.c0 raw2_2_0=_
    simp only [s2_2,raw2_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1259360088#u32 897654868#u32 81058558#u32 1409606157#u32)=ok s2_3.c1 := by
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
def value2 : FIo_Install.NE := ⟨⟨⟨265973361#u32,316861702#u32⟩,⟨587294079#u32,1672129241#u32⟩⟩,⟨⟨1247826479#u32,1305573439#u32⟩,⟨63739914#u32,1217835808#u32⟩⟩⟩
theorem finish2 : FIo_Native.fast_pairing.EbyKDot.finish s2_3=ok value2 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s2_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11003391596%2147483647 at h0
  norm_num at h0
  have e0 : a0=265973361#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=8906796290%2147483647 at h1
  norm_num at h1
  have e1 : a1=316861702#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15619679608%2147483647 at h2
  norm_num at h2
  have e2 : a2=587294079#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10262063829%2147483647 at h3
  norm_num at h3
  have e3 : a3=1672129241#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9837761067%2147483647 at h4
  norm_num at h4
  have e4 : a4=1247826479#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5600540733%2147483647 at h5
  norm_num at h5
  have e5 : a5=1305573439#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=12948641796%2147483647 at h6
  norm_num at h6
  have e6 : a6=63739914#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=11955254043%2147483647 at h7
  norm_num at h7
  have e7 : a7=1217835808#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value2 := Subtype.ext h
  have same : out=value2 := JFw_TX2_CellUnique.source out value2 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish2
theorem source2 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨7,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JGw_Tails07.value0_2
      from JGw_Tails07.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JGw_Tails07.value1_2
      from JGw_Tails07.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JGw_Tails07.value2_2
      from JGw_Tails07.source2_2,
    push2_0,push2_1,push2_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish2]
#print axioms source2
def s3_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s3_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 4203329827#u64 4868182439#u64 5095310259#u64 4951747810#u64)⟩,⟨(pack 3051250820#u64 2304610721#u64 5649618026#u64 5097884671#u64)⟩,1#usize⟩
def raw3_0_0 : Array U64 4#usize := (pack 6169032341572295854#u64 6269007373976377260#u64 10823975566374816471#u64 8899533831416229670#u64)
theorem pair3_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1862935332#u32 1665587764#u32 1626200354#u32 2072554177#u32)=ok raw3_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_0
def raw3_0_1 : Array U64 4#usize := (pack 3372117626028691018#u64 3063135311624711925#u64 7720763988655669385#u64 10256480747547188787#u64)
theorem pair3_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1862935332#u32 1665587764#u32 1626200354#u32 2072554177#u32)=ok raw3_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_1
theorem push3_0 : FIo_Native.fast_pairing.EbyKDot.push s3_0 JFw_TX2_P28.value
    JGw_Tails07.value0_3=ok (.Ok (),s3_1) := by
  have full : ¬s3_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value0_3=
      ok (.Ok (pack 1862935332#u32 1665587764#u32 1626200354#u32 2072554177#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1862935332<2147483647 ∧ 1665587764<2147483647) ∧ (1626200354<2147483647 ∧ 2072554177<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1862935332#u32 1665587764#u32 1626200354#u32 2072554177#u32)=ok s3_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_0.c0 raw3_0_0=_
    simp only [s3_0,raw3_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1862935332#u32 1665587764#u32 1626200354#u32 2072554177#u32)=ok s3_1.c1 := by
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
def s3_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 8301234078#u64 7263643775#u64 11001252954#u64 7789995700#u64)⟩,⟨(pack 6334694927#u64 3389405040#u64 10419153536#u64 7754237651#u64)⟩,2#usize⟩
def raw3_1_0 : Array U64 4#usize := (pack 5925054014206837764#u64 3262989419182221227#u64 10673951328813878347#u64 6072399944073951915#u64)
theorem pair3_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 981665121#u32 1523237363#u32 1239973531#u32 1072654285#u32)=ok raw3_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_0
def raw3_1_1 : Array U64 4#usize := (pack 4879506279355541332#u64 1217460730993709476#u64 9347826258783045933#u64 2249562599041835085#u64)
theorem pair3_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 981665121#u32 1523237363#u32 1239973531#u32 1072654285#u32)=ok raw3_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_1
theorem push3_1 : FIo_Native.fast_pairing.EbyKDot.push s3_1 JFw_TX2_P26.value
    JGw_Tails07.value1_3=ok (.Ok (),s3_2) := by
  have full : ¬s3_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value1_3=
      ok (.Ok (pack 981665121#u32 1523237363#u32 1239973531#u32 1072654285#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (981665121<2147483647 ∧ 1523237363<2147483647) ∧ (1239973531<2147483647 ∧ 1072654285<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 981665121#u32 1523237363#u32 1239973531#u32 1072654285#u32)=ok s3_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_1.c0 raw3_1_0=_
    simp only [s3_1,raw3_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 981665121#u32 1523237363#u32 1239973531#u32 1072654285#u32)=ok s3_2.c1 := by
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
def s3_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 11773104233#u64 9393188557#u64 16749511381#u64 9758943400#u64)⟩,⟨(pack 9799565653#u64 6924652866#u64 15927544001#u64 12520724653#u64)⟩,3#usize⟩
def raw3_2_0 : Array U64 4#usize := (pack 4109208894706997596#u64 1539543118996777392#u64 8570287439808030834#u64 3264984351606875652#u64)
theorem pair3_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1058865115#u32 1853065647#u32 784293685#u32 962445272#u32)=ok raw3_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_0
def raw3_2_1 : Array U64 4#usize := (pack 3066779618303734694#u64 5245951619968589674#u64 7699177521549503470#u64 9036124524303436568#u64)
theorem pair3_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1058865115#u32 1853065647#u32 784293685#u32 962445272#u32)=ok raw3_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_1
theorem push3_2 : FIo_Native.fast_pairing.EbyKDot.push s3_2 JFw_TX2_P27.value
    JGw_Tails07.value2_3=ok (.Ok (),s3_3) := by
  have full : ¬s3_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails07.value2_3=
      ok (.Ok (pack 1058865115#u32 1853065647#u32 784293685#u32 962445272#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1058865115<2147483647 ∧ 1853065647<2147483647) ∧ (784293685<2147483647 ∧ 962445272<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1058865115#u32 1853065647#u32 784293685#u32 962445272#u32)=ok s3_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_2.c0 raw3_2_0=_
    simp only [s3_2,raw3_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1058865115#u32 1853065647#u32 784293685#u32 962445272#u32)=ok s3_3.c1 := by
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
def value3 : FIo_Install.NE := ⟨⟨⟨1035685998#u32,803253969#u32⟩,⟨1717125852#u32,1169008812#u32⟩⟩,⟨⟨1209631065#u32,482201925#u32⟩,⟨895158472#u32,1783306418#u32⟩⟩⟩
theorem finish3 : FIo_Native.fast_pairing.EbyKDot.finish s3_3=ok value3 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s3_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11773104233%2147483647 at h0
  norm_num at h0
  have e0 : a0=1035685998#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=9393188557%2147483647 at h1
  norm_num at h1
  have e1 : a1=803253969#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16749511381%2147483647 at h2
  norm_num at h2
  have e2 : a2=1717125852#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9758943400%2147483647 at h3
  norm_num at h3
  have e3 : a3=1169008812#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9799565653%2147483647 at h4
  norm_num at h4
  have e4 : a4=1209631065#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6924652866%2147483647 at h5
  norm_num at h5
  have e5 : a5=482201925#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15927544001%2147483647 at h6
  norm_num at h6
  have e6 : a6=895158472#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=12520724653%2147483647 at h7
  norm_num at h7
  have e7 : a7=1783306418#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value3 := Subtype.ext h
  have same : out=value3 := JFw_TX2_CellUnique.source out value3 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish3
theorem source3 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨7,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JGw_Tails07.value0_3
      from JGw_Tails07.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JGw_Tails07.value1_3
      from JGw_Tails07.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JGw_Tails07.value2_3
      from JGw_Tails07.source2_3,
    push3_0,push3_1,push3_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish3]
#print axioms source3
end AspisR1.JHa_Tails7
end
