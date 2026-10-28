import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFw_TX2_CellUnique
import NDO_JGw_Tails05
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Tails5
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def s0_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s0_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 3421178909#u64 1607473945#u64 4379869330#u64 1738546171#u64)⟩,⟨(pack 2849990006#u64 1511598679#u64 4601078383#u64 2110685079#u64)⟩,1#usize⟩
def raw0_0_0 : Array U64 4#usize := (pack 4822457918996704323#u64 771833318288385657#u64 8643644197773424478#u64 1936668804064952307#u64)
theorem pair0_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 235448851#u32 200921301#u32 133120478#u32 695272015#u32)=ok raw0_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_0
def raw0_0_1 : Array U64 4#usize := (pack 4466950481077587423#u64 382850514913122640#u64 8481836749064228676#u64 1380279888413394202#u64)
theorem pair0_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 235448851#u32 200921301#u32 133120478#u32 695272015#u32)=ok raw0_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_1
theorem push0_0 : FIo_Native.fast_pairing.EbyKDot.push s0_0 JFw_TX2_P28.value
    JGw_Tails05.value0_0=ok (.Ok (),s0_1) := by
  have full : ¬s0_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value0_0=
      ok (.Ok (pack 235448851#u32 200921301#u32 133120478#u32 695272015#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (235448851<2147483647 ∧ 200921301<2147483647) ∧ (133120478<2147483647 ∧ 695272015<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 235448851#u32 200921301#u32 133120478#u32 695272015#u32)=ok s0_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_0.c0 raw0_0_0=_
    simp only [s0_0,raw0_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 235448851#u32 200921301#u32 133120478#u32 695272015#u32)=ok s0_1.c1 := by
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
def s0_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 6844698924#u64 1944765758#u64 11583607060#u64 5684402084#u64)⟩,⟨(pack 5503847712#u64 3780634721#u64 10952447890#u64 5175545901#u64)⟩,2#usize⟩
def raw0_1_0 : Array U64 4#usize := (pack 6876080851847038682#u64 490510038683443605#u64 12002427062523392222#u64 5955734719929971025#u64)
theorem pair0_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1193342668#u32 28067465#u32 940608854#u32 2101821453#u32)=ok raw0_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_0
def raw0_1_1 : Array U64 4#usize := (pack 5374396582416565563#u64 304152247247150164#u64 9858762737959533616#u64 2274645848397429733#u64)
theorem pair0_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1193342668#u32 28067465#u32 940608854#u32 2101821453#u32)=ok raw0_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_1
theorem push0_1 : FIo_Native.fast_pairing.EbyKDot.push s0_1 JFw_TX2_P26.value
    JGw_Tails05.value1_0=ok (.Ok (),s0_2) := by
  have full : ¬s0_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value1_0=
      ok (.Ok (pack 1193342668#u32 28067465#u32 940608854#u32 2101821453#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1193342668<2147483647 ∧ 28067465<2147483647) ∧ (940608854<2147483647 ∧ 2101821453<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1193342668#u32 28067465#u32 940608854#u32 2101821453#u32)=ok s0_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_1.c0 raw0_1_0=_
    simp only [s0_1,raw0_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1193342668#u32 28067465#u32 940608854#u32 2101821453#u32)=ok s0_2.c1 := by
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
def s0_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 10942911089#u64 2132747869#u64 16442835260#u64 7965054906#u64)⟩,⟨(pack 8763074966#u64 6221855212#u64 16819375584#u64 9507822467#u64)⟩,3#usize⟩
def raw0_2_0 : Array U64 4#usize := (pack 4741824427034480867#u64 258300741998414543#u64 9710089767820958147#u64 2256012239382385083#u64)
theorem pair0_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 367415217#u32 101479107#u32 2079695369#u32 1426022855#u32)=ok raw0_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_0
def raw0_2_1 : Array U64 4#usize := (pack 5076321083257155124#u64 859096649977942488#u64 10875441932597169324#u64 7262380452527667776#u64)
theorem pair0_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 367415217#u32 101479107#u32 2079695369#u32 1426022855#u32)=ok raw0_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_1
theorem push0_2 : FIo_Native.fast_pairing.EbyKDot.push s0_2 JFw_TX2_P27.value
    JGw_Tails05.value2_0=ok (.Ok (),s0_3) := by
  have full : ¬s0_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value2_0=
      ok (.Ok (pack 367415217#u32 101479107#u32 2079695369#u32 1426022855#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (367415217<2147483647 ∧ 101479107<2147483647) ∧ (2079695369<2147483647 ∧ 1426022855<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 367415217#u32 101479107#u32 2079695369#u32 1426022855#u32)=ok s0_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_2.c0 raw0_2_0=_
    simp only [s0_2,raw0_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 367415217#u32 101479107#u32 2079695369#u32 1426022855#u32)=ok s0_3.c1 := by
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
def value0 : FIo_Install.NE := ⟨⟨⟨205492854#u32,2132747869#u32⟩,⟨1410449731#u32,1522603965#u32⟩⟩,⟨⟨173140378#u32,1926887918#u32⟩,⟨1786990055#u32,917887879#u32⟩⟩⟩
theorem finish0 : FIo_Native.fast_pairing.EbyKDot.finish s0_3=ok value0 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s0_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10942911089%2147483647 at h0
  norm_num at h0
  have e0 : a0=205492854#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=2132747869%2147483647 at h1
  norm_num at h1
  have e1 : a1=2132747869#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16442835260%2147483647 at h2
  norm_num at h2
  have e2 : a2=1410449731#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=7965054906%2147483647 at h3
  norm_num at h3
  have e3 : a3=1522603965#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8763074966%2147483647 at h4
  norm_num at h4
  have e4 : a4=173140378#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6221855212%2147483647 at h5
  norm_num at h5
  have e5 : a5=1926887918#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16819375584%2147483647 at h6
  norm_num at h6
  have e6 : a6=1786990055#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=9507822467%2147483647 at h7
  norm_num at h7
  have e7 : a7=917887879#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value0 := Subtype.ext h
  have same : out=value0 := JFw_TX2_CellUnique.source out value0 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish0
theorem source0 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨5,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JGw_Tails05.value0_0
      from JGw_Tails05.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JGw_Tails05.value1_0
      from JGw_Tails05.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JGw_Tails05.value2_0
      from JGw_Tails05.source2_0,
    push0_0,push0_1,push0_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish0]
#print axioms source0
def s1_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s1_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 4427352149#u64 4051490851#u64 6334278579#u64 3237537939#u64)⟩,⟨(pack 1935790199#u64 1987069786#u64 4978455585#u64 4308669343#u64)⟩,1#usize⟩
def raw1_0_0 : Array U64 4#usize := (pack 6124723839988744338#u64 6029613646460607695#u64 9587365193448626178#u64 3638805801347949410#u64)
theorem pair1_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1796643982#u32 1598683077#u32 115364296#u32 677411191#u32)=ok raw1_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_0
def raw1_0_1 : Array U64 4#usize := (pack 3425729025879608235#u64 2950720815186453877#u64 8784750265722588284#u64 7476796975146024231#u64)
theorem pair1_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1796643982#u32 1598683077#u32 115364296#u32 677411191#u32)=ok raw1_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_1
theorem push1_0 : FIo_Native.fast_pairing.EbyKDot.push s1_0 JFw_TX2_P28.value
    JGw_Tails05.value0_1=ok (.Ok (),s1_1) := by
  have full : ¬s1_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value0_1=
      ok (.Ok (pack 1796643982#u32 1598683077#u32 115364296#u32 677411191#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1796643982<2147483647 ∧ 1598683077<2147483647) ∧ (115364296<2147483647 ∧ 677411191<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1796643982#u32 1598683077#u32 115364296#u32 677411191#u32)=ok s1_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_0.c0 raw1_0_0=_
    simp only [s1_0,raw1_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1796643982#u32 1598683077#u32 115364296#u32 677411191#u32)=ok s1_1.c1 := by
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
def s1_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 8544925438#u64 7498884033#u64 10759720442#u64 8301797280#u64)⟩,⟨(pack 5918466935#u64 2906387779#u64 9913724787#u64 6056445509#u64)⟩,2#usize⟩
def raw1_1_0 : Array U64 4#usize := (pack 5296649526158440781#u64 3850696711632204571#u64 8674869769687546391#u64 7746743890896914945#u64)
theorem pair1_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 720852287#u32 1881668573#u32 807864532#u32 1930787038#u32)=ok raw1_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_0
def raw1_1_1 : Array U64 4#usize := (pack 4625421248359381700#u64 1386049342557861080#u64 8539013692625839078#u64 2715257636157120968#u64)
theorem pair1_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 720852287#u32 1881668573#u32 807864532#u32 1930787038#u32)=ok raw1_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_1
theorem push1_1 : FIo_Native.fast_pairing.EbyKDot.push s1_1 JFw_TX2_P26.value
    JGw_Tails05.value1_1=ok (.Ok (),s1_2) := by
  have full : ¬s1_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value1_1=
      ok (.Ok (pack 720852287#u32 1881668573#u32 807864532#u32 1930787038#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (720852287<2147483647 ∧ 1881668573<2147483647) ∧ (807864532<2147483647 ∧ 1930787038<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 720852287#u32 1881668573#u32 807864532#u32 1930787038#u32)=ok s1_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_1.c0 raw1_1_0=_
    simp only [s1_1,raw1_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 720852287#u32 1881668573#u32 807864532#u32 1930787038#u32)=ok s1_2.c1 := by
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
def s1_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 12601811377#u64 8693154925#u64 15933714590#u64 11628402514#u64)⟩,⟨(pack 8901066033#u64 6973205949#u64 16852252010#u64 11185214042#u64)⟩,3#usize⟩
def raw1_2_0 : Array U64 4#usize := (pack 4317895779092442121#u64 1539316178432139483#u64 9570554441191522695#u64 3083351579818160089#u64)
theorem pair1_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1243311520#u32 1649062330#u32 1251267331#u32 151392602#u32)=ok raw1_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_0
def raw1_2_1 : Array U64 4#usize := (pack 3771164405192662435#u64 5224694616181377110#u64 10792360221625102614#u64 8362962637693411242#u64)
theorem pair1_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1243311520#u32 1649062330#u32 1251267331#u32 151392602#u32)=ok raw1_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_1
theorem push1_2 : FIo_Native.fast_pairing.EbyKDot.push s1_2 JFw_TX2_P27.value
    JGw_Tails05.value2_1=ok (.Ok (),s1_3) := by
  have full : ¬s1_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value2_1=
      ok (.Ok (pack 1243311520#u32 1649062330#u32 1251267331#u32 151392602#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1243311520<2147483647 ∧ 1649062330<2147483647) ∧ (1251267331<2147483647 ∧ 151392602<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1243311520#u32 1649062330#u32 1251267331#u32 151392602#u32)=ok s1_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_2.c0 raw1_2_0=_
    simp only [s1_2,raw1_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1243311520#u32 1649062330#u32 1251267331#u32 151392602#u32)=ok s1_3.c1 := by
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
def value1 : FIo_Install.NE := ⟨⟨⟨1864393142#u32,103220337#u32⟩,⟨901329061#u32,890984279#u32⟩⟩,⟨⟨311131445#u32,530755008#u32⟩,⟨1819866481#u32,447795807#u32⟩⟩⟩
theorem finish1 : FIo_Native.fast_pairing.EbyKDot.finish s1_3=ok value1 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s1_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=12601811377%2147483647 at h0
  norm_num at h0
  have e0 : a0=1864393142#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=8693154925%2147483647 at h1
  norm_num at h1
  have e1 : a1=103220337#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15933714590%2147483647 at h2
  norm_num at h2
  have e2 : a2=901329061#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=11628402514%2147483647 at h3
  norm_num at h3
  have e3 : a3=890984279#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8901066033%2147483647 at h4
  norm_num at h4
  have e4 : a4=311131445#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6973205949%2147483647 at h5
  norm_num at h5
  have e5 : a5=530755008#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16852252010%2147483647 at h6
  norm_num at h6
  have e6 : a6=1819866481#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=11185214042%2147483647 at h7
  norm_num at h7
  have e7 : a7=447795807#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value1 := Subtype.ext h
  have same : out=value1 := JFw_TX2_CellUnique.source out value1 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish1
theorem source1 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨5,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JGw_Tails05.value0_1
      from JGw_Tails05.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JGw_Tails05.value1_1
      from JGw_Tails05.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JGw_Tails05.value2_1
      from JGw_Tails05.source2_1,
    push1_0,push1_1,push1_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish1]
#print axioms source1
def s2_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s2_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 5681127527#u64 2364221185#u64 5521442351#u64 2663240671#u64)⟩,⟨(pack 2784124217#u64 2237134856#u64 6741861301#u64 3997535536#u64)⟩,1#usize⟩
def raw2_0_0 : Array U64 4#usize := (pack 7776760301240052691#u64 3510093941435166546#u64 10666132248128854182#u64 1832516238952170561#u64)
theorem pair2_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1776352960#u32 433312228#u32 182554919#u32 281308300#u32)=ok raw2_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_0
def raw2_0_1 : Array U64 4#usize := (pack 4866863664669210570#u64 2404307059737384696#u64 11697455058150832361#u64 4948622740600617181#u64)
theorem pair2_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1776352960#u32 433312228#u32 182554919#u32 281308300#u32)=ok raw2_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_1
theorem push2_0 : FIo_Native.fast_pairing.EbyKDot.push s2_0 JFw_TX2_P28.value
    JGw_Tails05.value0_2=ok (.Ok (),s2_1) := by
  have full : ¬s2_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value0_2=
      ok (.Ok (pack 1776352960#u32 433312228#u32 182554919#u32 281308300#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1776352960<2147483647 ∧ 433312228<2147483647) ∧ (182554919<2147483647 ∧ 281308300<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1776352960#u32 433312228#u32 182554919#u32 281308300#u32)=ok s2_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_0.c0 raw2_0_0=_
    simp only [s2_0,raw2_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1776352960#u32 433312228#u32 182554919#u32 281308300#u32)=ok s2_1.c1 := by
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
def s2_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 8438564803#u64 3858277407#u64 10836719642#u64 7305593541#u64)⟩,⟨(pack 5867858891#u64 4118598169#u64 11942229363#u64 6268352832#u64)⟩,2#usize⟩
def raw2_1_0 : Array U64 4#usize := (pack 4101448781445503869#u64 3182567946702027711#u64 7677936878715513881#u64 5449523909646056616#u64)
theorem pair2_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 51200252#u32 1659807187#u32 559753855#u32 1408191447#u32)=ok raw2_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_0
def raw2_1_1 : Array U64 4#usize := (pack 4246827940000466829#u64 1082476826784785457#u64 8322992888295515616#u64 1834621408188966698#u64)
theorem pair2_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 51200252#u32 1659807187#u32 559753855#u32 1408191447#u32)=ok raw2_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_1
theorem push2_1 : FIo_Native.fast_pairing.EbyKDot.push s2_1 JFw_TX2_P26.value
    JGw_Tails05.value1_2=ok (.Ok (),s2_2) := by
  have full : ¬s2_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value1_2=
      ok (.Ok (pack 51200252#u32 1659807187#u32 559753855#u32 1408191447#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (51200252<2147483647 ∧ 1659807187<2147483647) ∧ (559753855<2147483647 ∧ 1408191447<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 51200252#u32 1659807187#u32 559753855#u32 1408191447#u32)=ok s2_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_1.c0 raw2_1_0=_
    simp only [s2_1,raw2_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 51200252#u32 1659807187#u32 559753855#u32 1408191447#u32)=ok s2_2.c1 := by
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
def s2_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 12014976384#u64 5980566317#u64 15427653259#u64 8957958914#u64)⟩,⟨(pack 7574106552#u64 6551091643#u64 15371512429#u64 10268349538#u64)⟩,3#usize⟩
def raw2_2_0 : Array U64 4#usize := (pack 4194266624670410546#u64 1100632519213258795#u64 8097494967173508327#u64 2901804770915420188#u64)
theorem pair2_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 705495367#u32 1381604602#u32 599160523#u32 1742942172#u32)=ok raw2_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_0
def raw2_2_1 : Array U64 4#usize := (pack 3310789009303581645#u64 3756089681473456206#u64 6039101939407933067#u64 8430177350002350045#u64)
theorem pair2_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 705495367#u32 1381604602#u32 599160523#u32 1742942172#u32)=ok raw2_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_1
theorem push2_2 : FIo_Native.fast_pairing.EbyKDot.push s2_2 JFw_TX2_P27.value
    JGw_Tails05.value2_2=ok (.Ok (),s2_3) := by
  have full : ¬s2_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value2_2=
      ok (.Ok (pack 705495367#u32 1381604602#u32 599160523#u32 1742942172#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (705495367<2147483647 ∧ 1381604602<2147483647) ∧ (599160523<2147483647 ∧ 1742942172<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 705495367#u32 1381604602#u32 599160523#u32 1742942172#u32)=ok s2_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_2.c0 raw2_2_0=_
    simp only [s2_2,raw2_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 705495367#u32 1381604602#u32 599160523#u32 1742942172#u32)=ok s2_3.c1 := by
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
def value2 : FIo_Install.NE := ⟨⟨⟨1277558149#u32,1685599023#u32⟩,⟨395267730#u32,368024326#u32⟩⟩,⟨⟨1131655611#u32,108640702#u32⟩,⟨339126900#u32,1678414950#u32⟩⟩⟩
theorem finish2 : FIo_Native.fast_pairing.EbyKDot.finish s2_3=ok value2 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s2_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=12014976384%2147483647 at h0
  norm_num at h0
  have e0 : a0=1277558149#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5980566317%2147483647 at h1
  norm_num at h1
  have e1 : a1=1685599023#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15427653259%2147483647 at h2
  norm_num at h2
  have e2 : a2=395267730#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8957958914%2147483647 at h3
  norm_num at h3
  have e3 : a3=368024326#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=7574106552%2147483647 at h4
  norm_num at h4
  have e4 : a4=1131655611#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6551091643%2147483647 at h5
  norm_num at h5
  have e5 : a5=108640702#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15371512429%2147483647 at h6
  norm_num at h6
  have e6 : a6=339126900#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10268349538%2147483647 at h7
  norm_num at h7
  have e7 : a7=1678414950#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value2 := Subtype.ext h
  have same : out=value2 := JFw_TX2_CellUnique.source out value2 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish2
theorem source2 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨5,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JGw_Tails05.value0_2
      from JGw_Tails05.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JGw_Tails05.value1_2
      from JGw_Tails05.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JGw_Tails05.value2_2
      from JGw_Tails05.source2_2,
    push2_0,push2_1,push2_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish2]
#print axioms source2
def s3_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s3_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 5683123824#u64 3434971214#u64 7389122686#u64 2751763971#u64)⟩,⟨(pack 3967593808#u64 1915367057#u64 5922406954#u64 4348247922#u64)⟩,1#usize⟩
def raw3_0_0 : Array U64 4#usize := (pack 7784485347528637973#u64 5111987681548215522#u64 13980064701206674161#u64 5465078451785752120#u64)
theorem pair3_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 2127599870#u32 943874148#u32 1859692678#u32 570745939#u32)=ok raw3_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_0
def raw3_0_1 : Array U64 4#usize := (pack 4388591458205948917#u64 3069732591452449667#u64 11743134257148642659#u64 8946051872102250979#u64)
theorem pair3_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 2127599870#u32 943874148#u32 1859692678#u32 570745939#u32)=ok raw3_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_1
theorem push3_0 : FIo_Native.fast_pairing.EbyKDot.push s3_0 JFw_TX2_P28.value
    JGw_Tails05.value0_3=ok (.Ok (),s3_1) := by
  have full : ¬s3_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value0_3=
      ok (.Ok (pack 2127599870#u32 943874148#u32 1859692678#u32 570745939#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2127599870<2147483647 ∧ 943874148<2147483647) ∧ (1859692678<2147483647 ∧ 570745939<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 2127599870#u32 943874148#u32 1859692678#u32 570745939#u32)=ok s3_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_0.c0 raw3_0_0=_
    simp only [s3_0,raw3_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 2127599870#u32 943874148#u32 1859692678#u32 570745939#u32)=ok s3_1.c1 := by
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
def s3_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 9705132765#u64 7551334936#u64 12661477956#u64 7077875821#u64)⟩,⟨(pack 6775134816#u64 4491471997#u64 11860332337#u64 7362059124#u64)⟩,2#usize⟩
def raw3_1_0 : Array U64 4#usize := (pack 7789431765210742422#u64 4800542290728505916#u64 9803745268848784644#u64 7773903002025743163#u64)
theorem pair3_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2074395416#u32 2119935703#u32 303731911#u32 924201088#u32)=ok raw3_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_0
def raw3_1_1 : Array U64 4#usize := (pack 5441038446155187657#u64 1864134752996344976#u64 8941685813951794505#u64 2827448466679587126#u64)
theorem pair3_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2074395416#u32 2119935703#u32 303731911#u32 924201088#u32)=ok raw3_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_1
theorem push3_1 : FIo_Native.fast_pairing.EbyKDot.push s3_1 JFw_TX2_P26.value
    JGw_Tails05.value1_3=ok (.Ok (),s3_2) := by
  have full : ¬s3_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value1_3=
      ok (.Ok (pack 2074395416#u32 2119935703#u32 303731911#u32 924201088#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2074395416<2147483647 ∧ 2119935703<2147483647) ∧ (303731911<2147483647 ∧ 924201088<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2074395416#u32 2119935703#u32 303731911#u32 924201088#u32)=ok s3_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_1.c0 raw3_1_0=_
    simp only [s3_1,raw3_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2074395416#u32 2119935703#u32 303731911#u32 924201088#u32)=ok s3_2.c1 := by
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
def s3_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 11731768298#u64 10036401692#u64 16323768565#u64 8745453360#u64)⟩,⟨(pack 7396908522#u64 7544626040#u64 14928233060#u64 11257845866#u64)⟩,3#usize⟩
def raw3_2_0 : Array U64 4#usize := (pack 3596731746474242078#u64 1158464838305298625#u64 7787809018833168540#u64 2796865137104145079#u64)
theorem pair3_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 233212588#u32 2016330067#u32 822677553#u32 951485668#u32)=ok raw3_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_0
def raw3_2_1 : Array U64 4#usize := (pack 1299532994263762635#u64 4009970350655725928#u64 5732767105506259093#u64 7924447278901913429#u64)
theorem pair3_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 233212588#u32 2016330067#u32 822677553#u32 951485668#u32)=ok raw3_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_1
theorem push3_2 : FIo_Native.fast_pairing.EbyKDot.push s3_2 JFw_TX2_P27.value
    JGw_Tails05.value2_3=ok (.Ok (),s3_3) := by
  have full : ¬s3_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails05.value2_3=
      ok (.Ok (pack 233212588#u32 2016330067#u32 822677553#u32 951485668#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (233212588<2147483647 ∧ 2016330067<2147483647) ∧ (822677553<2147483647 ∧ 951485668<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 233212588#u32 2016330067#u32 822677553#u32 951485668#u32)=ok s3_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_2.c0 raw3_2_0=_
    simp only [s3_2,raw3_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 233212588#u32 2016330067#u32 822677553#u32 951485668#u32)=ok s3_3.c1 := by
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
def value3 : FIo_Install.NE := ⟨⟨⟨994350063#u32,1446467104#u32⟩,⟨1291383036#u32,155518772#u32⟩⟩,⟨⟨954457581#u32,1102175099#u32⟩,⟨2043331178#u32,520427631#u32⟩⟩⟩
theorem finish3 : FIo_Native.fast_pairing.EbyKDot.finish s3_3=ok value3 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s3_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11731768298%2147483647 at h0
  norm_num at h0
  have e0 : a0=994350063#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=10036401692%2147483647 at h1
  norm_num at h1
  have e1 : a1=1446467104#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16323768565%2147483647 at h2
  norm_num at h2
  have e2 : a2=1291383036#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8745453360%2147483647 at h3
  norm_num at h3
  have e3 : a3=155518772#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=7396908522%2147483647 at h4
  norm_num at h4
  have e4 : a4=954457581#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7544626040%2147483647 at h5
  norm_num at h5
  have e5 : a5=1102175099#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14928233060%2147483647 at h6
  norm_num at h6
  have e6 : a6=2043331178#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=11257845866%2147483647 at h7
  norm_num at h7
  have e7 : a7=520427631#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value3 := Subtype.ext h
  have same : out=value3 := JFw_TX2_CellUnique.source out value3 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish3
theorem source3 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨5,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JGw_Tails05.value0_3
      from JGw_Tails05.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JGw_Tails05.value1_3
      from JGw_Tails05.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨5,by decide⟩)
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JGw_Tails05.value2_3
      from JGw_Tails05.source2_3,
    push3_0,push3_1,push3_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish3]
#print axioms source3
end AspisR1.JHa_Tails5
end
