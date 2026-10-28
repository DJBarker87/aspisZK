import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFw_TX2_CellUnique
import NDO_JGw_Tails04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Tails4
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def s0_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s0_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 4319750988#u64 2642306425#u64 6011456122#u64 3194500160#u64)⟩,⟨(pack 2422974558#u64 2761230696#u64 4558356516#u64 2738531016#u64)⟩,1#usize⟩
def raw0_0_0 : Array U64 4#usize := (pack 6535560038047824088#u64 3618185102280992029#u64 10249827532737225423#u64 3739145505832172083#u64)
theorem pair0_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1402983900#u32 738120645#u32 570256485#u32 837566888#u32)=ok raw0_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_0
def raw0_0_1 : Array U64 4#usize := (pack 4320580806327145898#u64 2075992510403328264#u64 9776212646584571118#u64 5526584591035788281#u64)
theorem pair0_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1402983900#u32 738120645#u32 570256485#u32 837566888#u32)=ok raw0_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_0_1
theorem push0_0 : FIo_Native.fast_pairing.EbyKDot.push s0_0 JFw_TX2_P28.value
    JGw_Tails04.value0_0=ok (.Ok (),s0_1) := by
  have full : ¬s0_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value0_0=
      ok (.Ok (pack 1402983900#u32 738120645#u32 570256485#u32 837566888#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1402983900<2147483647 ∧ 738120645<2147483647) ∧ (570256485<2147483647 ∧ 837566888<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1402983900#u32 738120645#u32 570256485#u32 837566888#u32)=ok s0_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_0.c0 raw0_0_0=_
    simp only [s0_0,raw0_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1402983900#u32 738120645#u32 570256485#u32 837566888#u32)=ok s0_1.c1 := by
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
def s0_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 8551919877#u64 4214711296#u64 10925234820#u64 6851086197#u64)⟩,⟨(pack 6422636084#u64 3955369641#u64 9213192368#u64 5037522143#u64)⟩,2#usize⟩
def raw0_1_0 : Array U64 4#usize := (pack 7259084219648237683#u64 1829752714170454459#u64 10345747723411217039#u64 5546341024894415784#u64)
theorem pair0_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1517299715#u32 668424510#u32 105955895#u32 1320190274#u32)=ok raw0_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_0
def raw0_1_1 : Array U64 4#usize := (pack 5429776909958454061#u64 794694458118404213#u64 9291469097995816119#u64 2049948556267229028#u64)
theorem pair0_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1517299715#u32 668424510#u32 105955895#u32 1320190274#u32)=ok raw0_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_1_1
theorem push0_1 : FIo_Native.fast_pairing.EbyKDot.push s0_1 JFw_TX2_P26.value
    JGw_Tails04.value1_0=ok (.Ok (),s0_2) := by
  have full : ¬s0_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value1_0=
      ok (.Ok (pack 1517299715#u32 668424510#u32 105955895#u32 1320190274#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1517299715<2147483647 ∧ 668424510<2147483647) ∧ (105955895<2147483647 ∧ 1320190274<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1517299715#u32 668424510#u32 105955895#u32 1320190274#u32)=ok s0_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_1.c0 raw0_1_0=_
    simp only [s0_1,raw0_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1517299715#u32 668424510#u32 105955895#u32 1320190274#u32)=ok s0_2.c1 := by
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
def s0_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 10849235075#u64 5516194891#u64 15277775410#u64 8469907059#u64)⟩,⟨(pack 10219976383#u64 6571550317#u64 15115172830#u64 8935923220#u64)⟩,3#usize⟩
def raw0_2_0 : Array U64 4#usize := (pack 4830242627697594198#u64 1152102590399963620#u64 9211964395473571343#u64 2486966913032669320#u64)
theorem pair0_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1318539018#u32 806059957#u32 364882006#u32 1222297498#u32)=ok raw0_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_0
def raw0_2_1 : Array U64 4#usize := (pack 5462532598082908066#u64 3867376577064493761#u64 8942181352209845775#u64 6970407377151797261#u64)
theorem pair0_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1318539018#u32 806059957#u32 364882006#u32 1222297498#u32)=ok raw0_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair0_2_1
theorem push0_2 : FIo_Native.fast_pairing.EbyKDot.push s0_2 JFw_TX2_P27.value
    JGw_Tails04.value2_0=ok (.Ok (),s0_3) := by
  have full : ¬s0_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s0_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value2_0=
      ok (.Ok (pack 1318539018#u32 806059957#u32 364882006#u32 1222297498#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1318539018<2147483647 ∧ 806059957<2147483647) ∧ (364882006<2147483647 ∧ 1222297498<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1318539018#u32 806059957#u32 364882006#u32 1222297498#u32)=ok s0_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s0_2.c0 raw0_2_0=_
    simp only [s0_2,raw0_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s0_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1318539018#u32 806059957#u32 364882006#u32 1222297498#u32)=ok s0_3.c1 := by
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
def value0 : FIo_Install.NE := ⟨⟨⟨111816840#u32,1221227597#u32⟩,⟨245389881#u32,2027456118#u32⟩⟩,⟨⟨1630041795#u32,129099376#u32⟩,⟨82787301#u32,345988632#u32⟩⟩⟩
theorem finish0 : FIo_Native.fast_pairing.EbyKDot.finish s0_3=ok value0 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s0_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10849235075%2147483647 at h0
  norm_num at h0
  have e0 : a0=111816840#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5516194891%2147483647 at h1
  norm_num at h1
  have e1 : a1=1221227597#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15277775410%2147483647 at h2
  norm_num at h2
  have e2 : a2=245389881#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8469907059%2147483647 at h3
  norm_num at h3
  have e3 : a3=2027456118#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10219976383%2147483647 at h4
  norm_num at h4
  have e4 : a4=1630041795#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6571550317%2147483647 at h5
  norm_num at h5
  have e5 : a5=129099376#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15115172830%2147483647 at h6
  norm_num at h6
  have e6 : a6=82787301#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=8935923220%2147483647 at h7
  norm_num at h7
  have e7 : a7=345988632#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value0 := Subtype.ext h
  have same : out=value0 := JFw_TX2_CellUnique.source out value0 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish0
theorem source0 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨4,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JGw_Tails04.value0_0
      from JGw_Tails04.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JGw_Tails04.value1_0
      from JGw_Tails04.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JGw_Tails04.value2_0
      from JGw_Tails04.source2_0,
    push0_0,push0_1,push0_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish0]
#print axioms source0
def s1_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s1_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 3559207081#u64 908426481#u64 6343534476#u64 1340518262#u64)⟩,⟨(pack 2856963168#u64 679360230#u64 5802769268#u64 2400435337#u64)⟩,1#usize⟩
def raw1_0_0 : Array U64 4#usize := (pack 4519221958184153039#u64 1781592897346503255#u64 9978101249631320860#u64 1636277191249247383#u64)
theorem pair1_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 358334524#u32 589838970#u32 414218589#u32 180492028#u32)=ok raw1_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_0
def raw1_0_1 : Array U64 4#usize := (pack 4037929638355703079#u64 709698826529374273#u64 8688986080872252889#u64 2554637877332668751#u64)
theorem pair1_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 358334524#u32 589838970#u32 414218589#u32 180492028#u32)=ok raw1_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_0_1
theorem push1_0 : FIo_Native.fast_pairing.EbyKDot.push s1_0 JFw_TX2_P28.value
    JGw_Tails04.value0_1=ok (.Ok (),s1_1) := by
  have full : ¬s1_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value0_1=
      ok (.Ok (pack 358334524#u32 589838970#u32 414218589#u32 180492028#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (358334524<2147483647 ∧ 589838970<2147483647) ∧ (414218589<2147483647 ∧ 180492028<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 358334524#u32 589838970#u32 414218589#u32 180492028#u32)=ok s1_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_0.c0 raw1_0_0=_
    simp only [s1_0,raw1_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 358334524#u32 589838970#u32 414218589#u32 180492028#u32)=ok s1_1.c1 := by
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
def s1_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 7868589720#u64 2593102371#u64 12578088891#u64 5007119819#u64)⟩,⟨(pack 7403682426#u64 2207203989#u64 11469991540#u64 4588831773#u64)⟩,2#usize⟩
def raw1_1_0 : Array U64 4#usize := (pack 8271875606158032860#u64 2666001142985197918#u64 12493144244025466672#u64 5976259814297961743#u64)
theorem pair1_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2111003906#u32 993076175#u32 875119870#u32 734227797#u32)=ok raw1_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_0
def raw1_1_1 : Array U64 4#usize := (pack 5734761125008212067#u64 1146338284956275326#u64 10015595299819347272#u64 2344637222954508625#u64)
theorem pair1_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2111003906#u32 993076175#u32 875119870#u32 734227797#u32)=ok raw1_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_1_1
theorem push1_1 : FIo_Native.fast_pairing.EbyKDot.push s1_1 JFw_TX2_P26.value
    JGw_Tails04.value1_1=ok (.Ok (),s1_2) := by
  have full : ¬s1_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value1_1=
      ok (.Ok (pack 2111003906#u32 993076175#u32 875119870#u32 734227797#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2111003906<2147483647 ∧ 993076175<2147483647) ∧ (875119870<2147483647 ∧ 734227797<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 2111003906#u32 993076175#u32 875119870#u32 734227797#u32)=ok s1_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_1.c0 raw1_1_0=_
    simp only [s1_1,raw1_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 2111003906#u32 993076175#u32 875119870#u32 734227797#u32)=ok s1_2.c1 := by
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
def s1_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 11605390175#u64 3511351599#u64 19345610720#u64 7853767796#u64)⟩,⟨(pack 10037853346#u64 3328157726#u64 17606521300#u64 7817104419#u64)⟩,3#usize⟩
def raw1_2_0 : Array U64 4#usize := (pack 4756899452637363989#u64 406986110945693600#u64 9943007267717046090#u64 2015835323815757714#u64)
theorem pair1_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 525960517#u32 218329325#u32 1801370500#u32 837783879#u32)=ok raw1_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_0
def raw1_2_1 : Array U64 4#usize := (pack 5141805134703724826#u64 1359492849163607667#u64 11591916320878657132#u64 6242488047387540586#u64)
theorem pair1_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 525960517#u32 218329325#u32 1801370500#u32 837783879#u32)=ok raw1_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair1_2_1
theorem push1_2 : FIo_Native.fast_pairing.EbyKDot.push s1_2 JFw_TX2_P27.value
    JGw_Tails04.value2_1=ok (.Ok (),s1_3) := by
  have full : ¬s1_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s1_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value2_1=
      ok (.Ok (pack 525960517#u32 218329325#u32 1801370500#u32 837783879#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (525960517<2147483647 ∧ 218329325<2147483647) ∧ (1801370500<2147483647 ∧ 837783879<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 525960517#u32 218329325#u32 1801370500#u32 837783879#u32)=ok s1_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s1_2.c0 raw1_2_0=_
    simp only [s1_2,raw1_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s1_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 525960517#u32 218329325#u32 1801370500#u32 837783879#u32)=ok s1_3.c1 := by
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
def value1 : FIo_Install.NE := ⟨⟨⟨867971940#u32,1363867952#u32⟩,⟨18257897#u32,1411316855#u32⟩⟩,⟨⟨1447918758#u32,1180674079#u32⟩,⟨426652124#u32,1374653478#u32⟩⟩⟩
theorem finish1 : FIo_Native.fast_pairing.EbyKDot.finish s1_3=ok value1 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s1_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11605390175%2147483647 at h0
  norm_num at h0
  have e0 : a0=867971940#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=3511351599%2147483647 at h1
  norm_num at h1
  have e1 : a1=1363867952#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=19345610720%2147483647 at h2
  norm_num at h2
  have e2 : a2=18257897#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=7853767796%2147483647 at h3
  norm_num at h3
  have e3 : a3=1411316855#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10037853346%2147483647 at h4
  norm_num at h4
  have e4 : a4=1447918758#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=3328157726%2147483647 at h5
  norm_num at h5
  have e5 : a5=1180674079#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=17606521300%2147483647 at h6
  norm_num at h6
  have e6 : a6=426652124#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=7817104419%2147483647 at h7
  norm_num at h7
  have e7 : a7=1374653478#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value1 := Subtype.ext h
  have same : out=value1 := JFw_TX2_CellUnique.source out value1 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish1
theorem source1 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨4,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JGw_Tails04.value0_1
      from JGw_Tails04.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JGw_Tails04.value1_1
      from JGw_Tails04.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JGw_Tails04.value2_1
      from JGw_Tails04.source2_1,
    push1_0,push1_1,push1_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish1]
#print axioms source1
def s2_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s2_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 4195652949#u64 4190347408#u64 6465974991#u64 5504649558#u64)⟩,⟨(pack 2232947863#u64 3105507158#u64 5506657962#u64 5157538257#u64)⟩,1#usize⟩
def raw2_0_0 : Array U64 4#usize := (pack 5875625892155211801#u64 6464139138455644152#u64 11873507781595666937#u64 9563723094177608287#u64)
theorem pair2_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1811597185#u32 1791868529#u32 2113124144#u32 2006341254#u32)=ok raw2_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_0
def raw2_0_1 : Array U64 4#usize := (pack 3192012685747124055#u64 3055722956937891753#u64 7652059930741294781#u64 10984929843736816341#u64)
theorem pair2_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1811597185#u32 1791868529#u32 2113124144#u32 2006341254#u32)=ok raw2_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_0_1
theorem push2_0 : FIo_Native.fast_pairing.EbyKDot.push s2_0 JFw_TX2_P28.value
    JGw_Tails04.value0_2=ok (.Ok (),s2_1) := by
  have full : ¬s2_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value0_2=
      ok (.Ok (pack 1811597185#u32 1791868529#u32 2113124144#u32 2006341254#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1811597185<2147483647 ∧ 1791868529<2147483647) ∧ (2113124144<2147483647 ∧ 2006341254<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1811597185#u32 1791868529#u32 2113124144#u32 2006341254#u32)=ok s2_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_0.c0 raw2_0_0=_
    simp only [s2_0,raw2_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1811597185#u32 1791868529#u32 2113124144#u32 2006341254#u32)=ok s2_1.c1 := by
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
def s2_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 7564670149#u64 6329202689#u64 12021019656#u64 8377863170#u64)⟩,⟨(pack 6456451949#u64 3667093694#u64 10665974289#u64 7959084195#u64)⟩,2#usize⟩
def raw2_1_0 : Array U64 4#usize := (pack 5629595128047759758#u64 946025282320100731#u64 10472248823839290261#u64 5504301422528387254#u64)
theorem pair2_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 606964061#u32 379695486#u32 824470570#u32 2013054777#u32)=ok raw2_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_0
def raw2_1_1 : Array U64 4#usize := (pack 4912025380348986553#u64 390313268744538549#u64 9334833635216125936#u64 2016609122258211891#u64)
theorem pair2_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 606964061#u32 379695486#u32 824470570#u32 2013054777#u32)=ok raw2_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_1_1
theorem push2_1 : FIo_Native.fast_pairing.EbyKDot.push s2_1 JFw_TX2_P26.value
    JGw_Tails04.value1_2=ok (.Ok (),s2_2) := by
  have full : ¬s2_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value1_2=
      ok (.Ok (pack 606964061#u32 379695486#u32 824470570#u32 2013054777#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (606964061<2147483647 ∧ 379695486<2147483647) ∧ (824470570<2147483647 ∧ 2013054777<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 606964061#u32 379695486#u32 824470570#u32 2013054777#u32)=ok s2_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_1.c0 raw2_1_0=_
    simp only [s2_1,raw2_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 606964061#u32 379695486#u32 824470570#u32 2013054777#u32)=ok s2_2.c1 := by
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
def s2_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 10804101117#u64 7597880485#u64 17523738893#u64 12530888306#u64)⟩,⟨(pack 10485329650#u64 8245343247#u64 15456449327#u64 16329184861#u64)⟩,3#usize⟩
def raw2_2_0 : Array U64 4#usize := (pack 4499166668214586042#u64 2012708783616251057#u64 8989046757169942585#u64 4899995473240756889#u64)
theorem pair2_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1866031691#u32 1890941561#u32 1561233753#u32 2063240043#u32)=ok raw2_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_0
def raw2_2_1 : Array U64 4#usize := (pack 4429513251661952475#u64 6804797171301584223#u64 8691541170935544788#u64 13982956952490784564#u64)
theorem pair2_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1866031691#u32 1890941561#u32 1561233753#u32 2063240043#u32)=ok raw2_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair2_2_1
theorem push2_2 : FIo_Native.fast_pairing.EbyKDot.push s2_2 JFw_TX2_P27.value
    JGw_Tails04.value2_2=ok (.Ok (),s2_3) := by
  have full : ¬s2_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s2_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value2_2=
      ok (.Ok (pack 1866031691#u32 1890941561#u32 1561233753#u32 2063240043#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1866031691<2147483647 ∧ 1890941561<2147483647) ∧ (1561233753<2147483647 ∧ 2063240043<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1866031691#u32 1890941561#u32 1561233753#u32 2063240043#u32)=ok s2_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair2_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s2_2.c0 raw2_2_0=_
    simp only [s2_2,raw2_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s2_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1866031691#u32 1890941561#u32 1561233753#u32 2063240043#u32)=ok s2_3.c1 := by
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
def value2 : FIo_Install.NE := ⟨⟨⟨66682882#u32,1155429544#u32⟩,⟨343869717#u32,1793470071#u32⟩⟩,⟨⟨1895395062#u32,1802892306#u32⟩,⟨424063798#u32,1296799332#u32⟩⟩⟩
theorem finish2 : FIo_Native.fast_pairing.EbyKDot.finish s2_3=ok value2 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s2_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10804101117%2147483647 at h0
  norm_num at h0
  have e0 : a0=66682882#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7597880485%2147483647 at h1
  norm_num at h1
  have e1 : a1=1155429544#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17523738893%2147483647 at h2
  norm_num at h2
  have e2 : a2=343869717#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=12530888306%2147483647 at h3
  norm_num at h3
  have e3 : a3=1793470071#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10485329650%2147483647 at h4
  norm_num at h4
  have e4 : a4=1895395062#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=8245343247%2147483647 at h5
  norm_num at h5
  have e5 : a5=1802892306#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15456449327%2147483647 at h6
  norm_num at h6
  have e6 : a6=424063798#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=16329184861%2147483647 at h7
  norm_num at h7
  have e7 : a7=1296799332#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value2 := Subtype.ext h
  have same : out=value2 := JFw_TX2_CellUnique.source out value2 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish2
theorem source2 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨4,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JGw_Tails04.value0_2
      from JGw_Tails04.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JGw_Tails04.value1_2
      from JGw_Tails04.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JGw_Tails04.value2_2
      from JGw_Tails04.source2_2,
    push2_0,push2_1,push2_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish2]
#print axioms source2
def s3_0 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,⟨(pack 0#u64 0#u64 0#u64 0#u64)⟩,0#usize⟩
def s3_1 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 4010366795#u64 1193003399#u64 5771280716#u64 3382132928#u64)⟩,⟨(pack 2285668987#u64 1712018499#u64 5523949907#u64 4546263491#u64)⟩,1#usize⟩
def raw3_0_0 : Array U64 4#usize := (pack 4899208892787875388#u64 2420296414474963967#u64 10874397963391304354#u64 5797356146837589850#u64)
theorem pair3_0_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 618907892#u32 711346029#u32 1502006562#u32 1296536847#u32)=ok raw3_0_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_0
def raw3_0_1 : Array U64 4#usize := (pack 4003254519984010478#u64 1088300063531630075#u64 8068032194696837186#u64 5200491333497832227#u64)
theorem pair3_0_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 618907892#u32 711346029#u32 1502006562#u32 1296536847#u32)=ok raw3_0_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_0_1
theorem push3_0 : FIo_Native.fast_pairing.EbyKDot.push s3_0 JFw_TX2_P28.value
    JGw_Tails04.value0_3=ok (.Ok (),s3_1) := by
  have full : ¬s3_0.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_0 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value0_3=
      ok (.Ok (pack 618907892#u32 711346029#u32 1502006562#u32 1296536847#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (618907892<2147483647 ∧ 711346029<2147483647) ∧ (1502006562<2147483647 ∧ 1296536847<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32),(pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32)]) 1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c0 (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 618907892#u32 711346029#u32 1502006562#u32 1296536847#u32)=ok s3_1.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_0_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_0.c0 raw3_0_0=_
    simp only [s3_0,raw3_0_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_0.c1 (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 618907892#u32 711346029#u32 1502006562#u32 1296536847#u32)=ok s3_1.c1 := by
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
def s3_2 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 6988519716#u64 4428430489#u64 11144252080#u64 6064151103#u64)⟩,⟨(pack 5061370565#u64 3431523484#u64 10589464168#u64 5877380185#u64)⟩,2#usize⟩
def raw3_1_0 : Array U64 4#usize := (pack 4714746785282045800#u64 2792665611993718251#u64 9850498294342027616#u64 4994956096980979017#u64)
theorem pair3_1_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 323597127#u32 1402923200#u32 1240376068#u32 1054251242#u32)=ok raw3_1_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_0
def raw3_1_1 : Array U64 4#usize := (pack 4484040293305078403#u64 982140216619502004#u64 9118553249146103129#u64 1806895673232094849#u64)
theorem pair3_1_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 323597127#u32 1402923200#u32 1240376068#u32 1054251242#u32)=ok raw3_1_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_1_1
theorem push3_1 : FIo_Native.fast_pairing.EbyKDot.push s3_1 JFw_TX2_P26.value
    JGw_Tails04.value1_3=ok (.Ok (),s3_2) := by
  have full : ¬s3_1.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_1 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value1_3=
      ok (.Ok (pack 323597127#u32 1402923200#u32 1240376068#u32 1054251242#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (323597127<2147483647 ∧ 1402923200<2147483647) ∧ (1240376068<2147483647 ∧ 1054251242<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32),(pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32)]) 1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c0 (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 323597127#u32 1402923200#u32 1240376068#u32 1054251242#u32)=ok s3_2.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_1_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_1.c0 raw3_1_0=_
    simp only [s3_1,raw3_1_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_1.c1 (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 323597127#u32 1402923200#u32 1240376068#u32 1054251242#u32)=ok s3_2.c1 := by
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
def s3_3 : FIo_Native.fast_pairing.EbyKDot := ⟨⟨(pack 10021087003#u64 5855841059#u64 16653554604#u64 8457858130#u64)⟩,⟨(pack 7322200366#u64 5557389959#u64 14825663377#u64 9236760899#u64)⟩,3#usize⟩
def raw3_2_0 : Array U64 4#usize := (pack 4428057686249705461#u64 209456184737155062#u64 7900637895245422688#u64 1395269743311787315#u64)
theorem pair3_2_0 : FIo_Native.fast_pairing.canonical.Q.raw (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 42060174#u32 364679239#u32 76833342#u32 1997335591#u32)=ok raw3_2_0 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_0
def raw3_2_1 : Array U64 4#usize := (pack 4012428722570494229#u64 725034240627341394#u64 5091077848826969217#u64 4539871248053328697#u64)
theorem pair3_2_1 : FIo_Native.fast_pairing.canonical.Q.raw (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 42060174#u32 364679239#u32 76833342#u32 1997335591#u32)=ok raw3_2_1 := by
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,
    JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms pair3_2_1
theorem push3_2 : FIo_Native.fast_pairing.EbyKDot.push s3_2 JFw_TX2_P27.value
    JGw_Tails04.value2_3=ok (.Ok (),s3_3) := by
  have full : ¬s3_2.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold s3_2 FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JGw_Tails04.value2_3=
      ok (.Ok (pack 42060174#u32 364679239#u32 76833342#u32 1997335591#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (42060174<2147483647 ∧ 364679239<2147483647) ∧ (76833342<2147483647 ∧ 1997335591<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [(pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32),(pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32)]) 1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c0 (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 42060174#u32 364679239#u32 76833342#u32 1997335591#u32)=ok s3_3.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair3_2_0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize} s3_2.c0 raw3_2_0=_
    simp only [s3_2,raw3_2_0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push s3_2.c1 (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 42060174#u32 364679239#u32 76833342#u32 1997335591#u32)=ok s3_3.c1 := by
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
def value3 : FIo_Install.NE := ⟨⟨⟨1431152415#u32,1560873765#u32⟩,⟨1621169075#u32,2015407189#u32⟩⟩,⟨⟨879749425#u32,1262422665#u32⟩,⟨1940761495#u32,646826311#u32⟩⟩⟩
theorem finish3 : FIo_Native.fast_pairing.EbyKDot.finish s3_3=ok value3 := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source s3_3
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10021087003%2147483647 at h0
  norm_num at h0
  have e0 : a0=1431152415#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5855841059%2147483647 at h1
  norm_num at h1
  have e1 : a1=1560873765#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16653554604%2147483647 at h2
  norm_num at h2
  have e2 : a2=1621169075#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8457858130%2147483647 at h3
  norm_num at h3
  have e3 : a3=2015407189#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=7322200366%2147483647 at h4
  norm_num at h4
  have e4 : a4=879749425#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5557389959%2147483647 at h5
  norm_num at h5
  have e5 : a5=1262422665#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14825663377%2147483647 at h6
  norm_num at h6
  have e6 : a6=1940761495#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=9236760899%2147483647 at h7
  norm_num at h7
  have e7 : a7=646826311#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value3 := Subtype.ext h
  have same : out=value3 := JFw_TX2_CellUnique.source out value3 (by intro j;rw [limbs])
  exact same ▸ run
#print axioms finish3
theorem source3 : JFs_TX2_DotSuffix.tail (JFr_TX2_Windows.array ⟨4,by decide⟩)
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
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JGw_Tails04.value0_3
      from JGw_Tails04.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JGw_Tails04.value1_3
      from JGw_Tails04.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array ⟨4,by decide⟩)
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JGw_Tails04.value2_3
      from JGw_Tails04.source2_3,
    push3_0,push3_1,push3_2,Aeneas.Std.uncurry,core.result.Result.unwrap,finish3]
#print axioms source3
end AspisR1.JHa_Tails4
end
