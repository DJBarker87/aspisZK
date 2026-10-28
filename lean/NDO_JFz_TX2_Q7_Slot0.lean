import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails17
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1333869254#u32,1240937178#u32⟩,⟨1731730504#u32,411531736#u32⟩⟩,⟨⟨437425436#u32,300633895#u32⟩,⟨362865925#u32,1507311181#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 7 0 0 0 26%2147483647=1333869254 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1111153578+855639275*932074484+867568255*252650691+352063*1624326703+1106523000*1673529604+1554033304*1684917233+1430280692*694244534+1491718280*552697128+118514350*1240680893+1675652887*911239636+1364884909*1690417804+1135303194*124316000+304762092*400350096+1465393816*1925062053+824208172*1864939993+1752653420*999995668+1385409049*1490474596+1003904973*699241366+1298953245*616803804+2005758375*832837911+497936241*1354854469+235809508*535676096+1478307182*62856500+1858903615*820200919+628035096*1845963729+1244951250*1727917617)%2147483647=1333869254
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 7 0 1 0 26%2147483647=1240937178 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1111153578+1483149559*932074484+655227887*252650691+39062738*1624326703+729079828*1673529604+67370206*1684917233+1685049618*694244534+385547620*552697128+1786803209*1240680893+779721715*911239636+594709522*1690417804+338788461*124316000+526756808*400350096+184076238*1925062053+1852498770*1864939993+2102463508*999995668+1086671526*1490474596+1147694576*699241366+1504805752*616803804+2005073905*832837911+185008025*1354854469+1485990146*535676096+1255280192*62856500+1018329259*820200919+570157693*1845963729+1511904630*1727917617)%2147483647=1240937178
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 7 0 2 0 26%2147483647=1731730504 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1111153578+1898717401*932074484+1032732628*252650691+1313565596*1624326703+1074182998*1673529604+1410213748*1684917233+1182702806*694244534+321711020*552697128+2062791928*1240680893+1188803754*911239636+2038502201*1690417804+735931834*124316000+1330533011*400350096+1052874750*1925062053+950153811*1864939993+1225424092*999995668+1659116453*1490474596+1474177753*699241366+2073609211*616803804+1602919019*832837911+1865917845*1354854469+1085624123*535676096+1837870964*62856500+1550509101*820200919+1661725734*1845963729+2066655336*1727917617)%2147483647=1731730504
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 7 0 3 0 26%2147483647=411531736 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1111153578+1849775942*932074484+656039795*252650691+1840648083*1624326703+246996287*1673529604+1369248953*1684917233+1132591724*694244534+92744917*552697128+1719480363*1240680893+1266677922*911239636+377386917*1690417804+735227219*124316000+465096431*400350096+451889791*1925062053+1379836302*1864939993+618598847*999995668+1624084534*1490474596+1511477847*699241366+1840812326*616803804+185546252*832837911+2145463598*1354854469+82870699*535676096+1625323762*62856500+1843639311*820200919+1777269271*1845963729+1645120956*1727917617)%2147483647=411531736
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 7 0 4 0 26%2147483647=437425436 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1111153578+1112406525*932074484+1345999435*252650691+752376469*1624326703+634588140*1673529604+1419170319*1684917233+1702860885*694244534+710076517*552697128+1256487405*1240680893+1114745059*911239636+1137838899*1690417804+1254184109*124316000+1038210451*400350096+274378589*1925062053+171986381*1864939993+1536678585*999995668+1305878831*1490474596+1335902916*699241366+1755193245*616803804+2023391453*832837911+293456010*1354854469+1751078325*535676096+1423042536*62856500+1749638204*820200919+1345811362*1845963729+1284924881*1727917617)%2147483647=437425436
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 7 0 5 0 26%2147483647=300633895 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1111153578+1796814865*932074484+1253123171*252650691+1317611639*1624326703+1559245386*1673529604+1866942376*1684917233+1973593402*694244534+47019780*552697128+1353487525*1240680893+1840161555*911239636+2003659556*1690417804+200559114*124316000+334988447*400350096+2023650872*1925062053+1296497964*1864939993+34285357*999995668+1685894190*1490474596+995962325*699241366+1295624230*616803804+1199631211*832837911+1948677857*1354854469+1425322328*535676096+1466877680*62856500+702011012*820200919+937706871*1845963729+455802666*1727917617)%2147483647=300633895
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 7 0 6 0 26%2147483647=362865925 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1111153578+1838939499*932074484+1353876630*252650691+1258713036*1624326703+1947503436*1673529604+1271796599*1684917233+1660157177*694244534+564707688*552697128+1858113864*1240680893+1015817431*911239636+1264608004*1690417804+735383960*124316000+221696734*400350096+1297524163*1925062053+109088572*1864939993+792206628*999995668+1921581249*1490474596+94118806*699241366+476103426*616803804+239612482*832837911+177052717*1354854469+826458039*535676096+1923715623*62856500+1014161165*820200919+1341609618*1845963729+786325583*1727917617)%2147483647=362865925
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 7 0 7 0 26%2147483647=1507311181 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1111153578+418714188*932074484+1675147475*252650691+1674326661*1624326703+547797802*1673529604+2073962627*1684917233+897270857*694244534+1582958967*552697128+49892701*1240680893+1256824732*911239636+1435903714*1690417804+742583315*124316000+1789294768*400350096+13407412*1925062053+518661610*1864939993+1259751297*999995668+1695663205*1490474596+2068940067*699241366+940478841*616803804+1982757556*832837911+1956713516*1354854469+863066484*535676096+522298462*62856500+1343575777*820200919+771712139*1845963729+157728743*1727917617)%2147483647=1507311181
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 7 0
  have same : out=value := JFw_TX2_CellUnique.source out value (by
    intro j
    fin_cases j
    · exact (h 0).trans lane0
    · exact (h 1).trans lane1
    · exact (h 2).trans lane2
    · exact (h 3).trans lane3
    · exact (h 4).trans lane4
    · exact (h 5).trans lane5
    · exact (h 6).trans lane6
    · exact (h 7).trans lane7
    )
  exact same ▸ run
#print axioms lane0
#print axioms lane1
#print axioms lane2
#print axioms lane3
#print axioms lane4
#print axioms lane5
#print axioms lane6
#print axioms lane7
#print axioms source
end AspisR1.JFz_TX2_Q7_Head0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw00
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3396341852#u64 3673695769#u64 4958618093#u64 2139333941#u64⟩,⟨pack 3569695922#u64 2688900339#u64 5067701155#u64 4340210490#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4385168119593275909#u64 3368647825653528423#u64 9543427708867600397#u64 3831509669787673016#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 661013421#u32 1126525014#u32 594708787#u32 812597813#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 661013421#u32) (JFs_TX2_RawMath.extend 1126525014#u32) (JFs_TX2_RawMath.extend 594708787#u32) (JFs_TX2_RawMath.extend 812597813#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 661013421#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 661013421#u32) (JFs_TX2_RawMath.extend 1126525014#u32) (JFs_TX2_RawMath.extend 594708787#u32) (JFs_TX2_RawMath.extend 812597813#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1126525014#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 661013421#u32) (JFs_TX2_RawMath.extend 1126525014#u32) (JFs_TX2_RawMath.extend 594708787#u32) (JFs_TX2_RawMath.extend 812597813#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 594708787#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 661013421#u32) (JFs_TX2_RawMath.extend 1126525014#u32) (JFs_TX2_RawMath.extend 594708787#u32) (JFs_TX2_RawMath.extend 812597813#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 812597813#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3505428079151000619#u64 1326368344973308669#u64 7484723280064074574#u64 4795152890829913839#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 661013421#u32 1126525014#u32 594708787#u32 812597813#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 661013421#u32) (JFs_TX2_RawMath.extend 1126525014#u32) (JFs_TX2_RawMath.extend 594708787#u32) (JFs_TX2_RawMath.extend 812597813#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 661013421#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 661013421#u32) (JFs_TX2_RawMath.extend 1126525014#u32) (JFs_TX2_RawMath.extend 594708787#u32) (JFs_TX2_RawMath.extend 812597813#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1126525014#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 661013421#u32) (JFs_TX2_RawMath.extend 1126525014#u32) (JFs_TX2_RawMath.extend 594708787#u32) (JFs_TX2_RawMath.extend 812597813#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 594708787#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 661013421#u32) (JFs_TX2_RawMath.extend 1126525014#u32) (JFs_TX2_RawMath.extend 594708787#u32) (JFs_TX2_RawMath.extend 812597813#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 812597813#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails17.value0_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value0_0=
      ok (.Ok (pack 661013421#u32 1126525014#u32 594708787#u32 812597813#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (661013421<2147483647 ∧ 1126525014<2147483647) ∧ (594708787<2147483647 ∧ 812597813<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 661013421#u32 1126525014#u32 594708787#u32 812597813#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 661013421#u32 1126525014#u32 594708787#u32 812597813#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q7_Raw00
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3396341852#u64 3673695769#u64 4958618093#u64 2139333941#u64⟩,⟨pack 3569695922#u64 2688900339#u64 5067701155#u64 4340210490#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7042427906#u64 5498996224#u64 9555794926#u64 4355108618#u64⟩,⟨pack 7844932747#u64 5096013545#u64 9220160705#u64 5943007311#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5004787628120847357#u64 1901743210301173032#u64 8560399408186396209#u64 3436776856713315622#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 383742630#u32 923970959#u32 135422019#u32 785202759#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 383742630#u32) (JFs_TX2_RawMath.extend 923970959#u32) (JFs_TX2_RawMath.extend 135422019#u32) (JFs_TX2_RawMath.extend 785202759#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 383742630#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 383742630#u32) (JFs_TX2_RawMath.extend 923970959#u32) (JFs_TX2_RawMath.extend 135422019#u32) (JFs_TX2_RawMath.extend 785202759#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 923970959#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 383742630#u32) (JFs_TX2_RawMath.extend 923970959#u32) (JFs_TX2_RawMath.extend 135422019#u32) (JFs_TX2_RawMath.extend 785202759#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 135422019#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 383742630#u32) (JFs_TX2_RawMath.extend 923970959#u32) (JFs_TX2_RawMath.extend 135422019#u32) (JFs_TX2_RawMath.extend 785202759#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 785202759#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4637629841361508432#u64 687740777901781191#u64 8771603470941389658#u64 1182634460927335816#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 383742630#u32 923970959#u32 135422019#u32 785202759#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 383742630#u32) (JFs_TX2_RawMath.extend 923970959#u32) (JFs_TX2_RawMath.extend 135422019#u32) (JFs_TX2_RawMath.extend 785202759#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 383742630#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 383742630#u32) (JFs_TX2_RawMath.extend 923970959#u32) (JFs_TX2_RawMath.extend 135422019#u32) (JFs_TX2_RawMath.extend 785202759#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 923970959#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 383742630#u32) (JFs_TX2_RawMath.extend 923970959#u32) (JFs_TX2_RawMath.extend 135422019#u32) (JFs_TX2_RawMath.extend 785202759#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 135422019#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 383742630#u32) (JFs_TX2_RawMath.extend 923970959#u32) (JFs_TX2_RawMath.extend 135422019#u32) (JFs_TX2_RawMath.extend 785202759#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 785202759#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails17.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value1_0=
      ok (.Ok (pack 383742630#u32 923970959#u32 135422019#u32 785202759#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (383742630<2147483647 ∧ 923970959<2147483647) ∧ (135422019<2147483647 ∧ 785202759<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 383742630#u32 923970959#u32 135422019#u32 785202759#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3396341852#u64 3673695769#u64 4958618093#u64 2139333941#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 383742630#u32 923970959#u32 135422019#u32 785202759#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3569695922#u64 2688900339#u64 5067701155#u64 4340210490#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q7_Raw01
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 7042427906#u64 5498996224#u64 9555794926#u64 4355108618#u64⟩,⟨pack 7844932747#u64 5096013545#u64 9220160705#u64 5943007311#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9212602905#u64 6400000129#u64 15438867626#u64 6477161018#u64⟩,⟨pack 11091622706#u64 8026331051#u64 15155600612#u64 10323412739#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4443369439211435050#u64 837920911342596415#u64 9849827335061460272#u64 2228865191919937798#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 669364908#u32 905857354#u32 1615509177#u32 129159159#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 669364908#u32) (JFs_TX2_RawMath.extend 905857354#u32) (JFs_TX2_RawMath.extend 1615509177#u32) (JFs_TX2_RawMath.extend 129159159#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 669364908#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 669364908#u32) (JFs_TX2_RawMath.extend 905857354#u32) (JFs_TX2_RawMath.extend 1615509177#u32) (JFs_TX2_RawMath.extend 129159159#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 905857354#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 669364908#u32) (JFs_TX2_RawMath.extend 905857354#u32) (JFs_TX2_RawMath.extend 1615509177#u32) (JFs_TX2_RawMath.extend 129159159#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1615509177#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 669364908#u32) (JFs_TX2_RawMath.extend 905857354#u32) (JFs_TX2_RawMath.extend 1615509177#u32) (JFs_TX2_RawMath.extend 129159159#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 129159159#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4125821383445894471#u64 2844866768733936193#u64 11618806150980111070#u64 6365887715936261224#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 669364908#u32 905857354#u32 1615509177#u32 129159159#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 669364908#u32) (JFs_TX2_RawMath.extend 905857354#u32) (JFs_TX2_RawMath.extend 1615509177#u32) (JFs_TX2_RawMath.extend 129159159#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 669364908#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 669364908#u32) (JFs_TX2_RawMath.extend 905857354#u32) (JFs_TX2_RawMath.extend 1615509177#u32) (JFs_TX2_RawMath.extend 129159159#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 905857354#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 669364908#u32) (JFs_TX2_RawMath.extend 905857354#u32) (JFs_TX2_RawMath.extend 1615509177#u32) (JFs_TX2_RawMath.extend 129159159#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1615509177#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 669364908#u32) (JFs_TX2_RawMath.extend 905857354#u32) (JFs_TX2_RawMath.extend 1615509177#u32) (JFs_TX2_RawMath.extend 129159159#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 129159159#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails17.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value2_0=
      ok (.Ok (pack 669364908#u32 905857354#u32 1615509177#u32 129159159#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (669364908<2147483647 ∧ 905857354<2147483647) ∧ (1615509177<2147483647 ∧ 129159159<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 669364908#u32 905857354#u32 1615509177#u32 129159159#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7042427906#u64 5498996224#u64 9555794926#u64 4355108618#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 669364908#u32 905857354#u32 1615509177#u32 129159159#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7844932747#u64 5096013545#u64 9220160705#u64 5943007311#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q7_Raw02
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Tail0
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨622668317#u32,2105032835#u32⟩,⟨406482097#u32,34710077#u32⟩⟩,⟨⟨354204471#u32,1583880110#u32⟩,⟨123215083#u32,1733478151#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q7_Raw02.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q7_Raw02.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9212602905%2147483647 at h0
  norm_num at h0
  have e0 : a0=622668317#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6400000129%2147483647 at h1
  norm_num at h1
  have e1 : a1=2105032835#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15438867626%2147483647 at h2
  norm_num at h2
  have e2 : a2=406482097#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=6477161018%2147483647 at h3
  norm_num at h3
  have e3 : a3=34710077#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=11091622706%2147483647 at h4
  norm_num at h4
  have e4 : a4=354204471#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=8026331051%2147483647 at h5
  norm_num at h5
  have e5 : a5=1583880110#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15155600612%2147483647 at h6
  norm_num at h6
  have e6 : a6=123215083#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10323412739%2147483647 at h7
  norm_num at h7
  have e7 : a7=1733478151#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q7_Raw00.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JFr_TX2_Tails17.value0_0
      from JFr_TX2_Tails17.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JFr_TX2_Tails17.value1_0
      from JFr_TX2_Tails17.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JFr_TX2_Tails17.value2_0
      from JFr_TX2_Tails17.source2_0,
    JFz_TX2_Q7_Raw00.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q7_Raw00.after=JFz_TX2_Q7_Raw01.before := rfl
  have same2 : JFz_TX2_Q7_Raw01.after=JFz_TX2_Q7_Raw02.before := rfl
  simp only [same1,JFz_TX2_Q7_Raw01.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q7_Raw02.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q7_Tail0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1956537571#u32,1198486366#u32⟩,⟨2138212601#u32,446241813#u32⟩⟩,⟨⟨791629907#u32,1884514005#u32⟩,⟨486081008#u32,1093305685#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1956537571<2147483647 ∧ 1198486366<2147483647) ∧ (2138212601<2147483647 ∧ 446241813<2147483647)) ∧
    ((791629907<2147483647 ∧ 1884514005<2147483647) ∧ (486081008<2147483647 ∧ 1093305685<2147483647))
  omega
theorem addition : decode JFz_TX2_Q7_Head0.value+decode JFz_TX2_Q7_Tail0.value=decode value := by
  change (⟨⟨⟨1333869254,1240937178⟩,⟨1731730504,411531736⟩⟩,⟨⟨437425436,300633895⟩,⟨362865925,1507311181⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨622668317,2105032835⟩,⟨406482097,34710077⟩⟩,⟨⟨354204471,1583880110⟩,⟨123215083,1733478151⟩⟩⟩=⟨⟨⟨1956537571,1198486366⟩,⟨2138212601,446241813⟩⟩,⟨⟨791629907,1884514005⟩,⟨486081008,1093305685⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 7 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q7_Head0.value JFz_TX2_Q7_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q7_Head0.source,
      JFz_TX2_Q7_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q7_Head0.value := by
    change ((1333869254<2147483647 ∧ 1240937178<2147483647) ∧ (1731730504<2147483647 ∧ 411531736<2147483647)) ∧
      ((437425436<2147483647 ∧ 300633895<2147483647) ∧ (362865925<2147483647 ∧ 1507311181<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q7_Tail0.value := by
    change ((622668317<2147483647 ∧ 2105032835<2147483647) ∧ (406482097<2147483647 ∧ 34710077<2147483647)) ∧
      ((354204471<2147483647 ∧ 1583880110<2147483647) ∧ (123215083<2147483647 ∧ 1733478151<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q7_Dot0
end
