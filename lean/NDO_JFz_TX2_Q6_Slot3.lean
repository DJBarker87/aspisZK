import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails16
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1209598717#u32,2077904122#u32⟩,⟨590842712#u32,131975397#u32⟩⟩,⟨⟨144159936#u32,777440282#u32⟩,⟨1812538172#u32,1342465241#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 6 3 0 0 26%2147483647=1209598717 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1591179681+855639275*309607049+867568255*546553877+352063*1056401817+1106523000*1078123924+1554033304*555906257+1430280692*681577324+1491718280*2011956623+118514350*1944422173+1675652887*1559246070+1364884909*1425248998+1135303194*1033352314+304762092*1619348998+1465393816*982725756+824208172*1657920947+1752653420*1498752791+1385409049*1065449082+1003904973*983776859+1298953245*1451701531+2005758375*2000958262+497936241*1610082924+235809508*1250308965+1478307182*1317170203+1858903615*751418916+628035096*938673626+1244951250*1444449623)%2147483647=1209598717
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 6 3 1 0 26%2147483647=2077904122 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1591179681+1483149559*309607049+655227887*546553877+39062738*1056401817+729079828*1078123924+67370206*555906257+1685049618*681577324+385547620*2011956623+1786803209*1944422173+779721715*1559246070+594709522*1425248998+338788461*1033352314+526756808*1619348998+184076238*982725756+1852498770*1657920947+2102463508*1498752791+1086671526*1065449082+1147694576*983776859+1504805752*1451701531+2005073905*2000958262+185008025*1610082924+1485990146*1250308965+1255280192*1317170203+1018329259*751418916+570157693*938673626+1511904630*1444449623)%2147483647=2077904122
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 6 3 2 0 26%2147483647=590842712 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1591179681+1898717401*309607049+1032732628*546553877+1313565596*1056401817+1074182998*1078123924+1410213748*555906257+1182702806*681577324+321711020*2011956623+2062791928*1944422173+1188803754*1559246070+2038502201*1425248998+735931834*1033352314+1330533011*1619348998+1052874750*982725756+950153811*1657920947+1225424092*1498752791+1659116453*1065449082+1474177753*983776859+2073609211*1451701531+1602919019*2000958262+1865917845*1610082924+1085624123*1250308965+1837870964*1317170203+1550509101*751418916+1661725734*938673626+2066655336*1444449623)%2147483647=590842712
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 6 3 3 0 26%2147483647=131975397 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1591179681+1849775942*309607049+656039795*546553877+1840648083*1056401817+246996287*1078123924+1369248953*555906257+1132591724*681577324+92744917*2011956623+1719480363*1944422173+1266677922*1559246070+377386917*1425248998+735227219*1033352314+465096431*1619348998+451889791*982725756+1379836302*1657920947+618598847*1498752791+1624084534*1065449082+1511477847*983776859+1840812326*1451701531+185546252*2000958262+2145463598*1610082924+82870699*1250308965+1625323762*1317170203+1843639311*751418916+1777269271*938673626+1645120956*1444449623)%2147483647=131975397
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 6 3 4 0 26%2147483647=144159936 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1591179681+1112406525*309607049+1345999435*546553877+752376469*1056401817+634588140*1078123924+1419170319*555906257+1702860885*681577324+710076517*2011956623+1256487405*1944422173+1114745059*1559246070+1137838899*1425248998+1254184109*1033352314+1038210451*1619348998+274378589*982725756+171986381*1657920947+1536678585*1498752791+1305878831*1065449082+1335902916*983776859+1755193245*1451701531+2023391453*2000958262+293456010*1610082924+1751078325*1250308965+1423042536*1317170203+1749638204*751418916+1345811362*938673626+1284924881*1444449623)%2147483647=144159936
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 6 3 5 0 26%2147483647=777440282 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1591179681+1796814865*309607049+1253123171*546553877+1317611639*1056401817+1559245386*1078123924+1866942376*555906257+1973593402*681577324+47019780*2011956623+1353487525*1944422173+1840161555*1559246070+2003659556*1425248998+200559114*1033352314+334988447*1619348998+2023650872*982725756+1296497964*1657920947+34285357*1498752791+1685894190*1065449082+995962325*983776859+1295624230*1451701531+1199631211*2000958262+1948677857*1610082924+1425322328*1250308965+1466877680*1317170203+702011012*751418916+937706871*938673626+455802666*1444449623)%2147483647=777440282
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 6 3 6 0 26%2147483647=1812538172 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1591179681+1838939499*309607049+1353876630*546553877+1258713036*1056401817+1947503436*1078123924+1271796599*555906257+1660157177*681577324+564707688*2011956623+1858113864*1944422173+1015817431*1559246070+1264608004*1425248998+735383960*1033352314+221696734*1619348998+1297524163*982725756+109088572*1657920947+792206628*1498752791+1921581249*1065449082+94118806*983776859+476103426*1451701531+239612482*2000958262+177052717*1610082924+826458039*1250308965+1923715623*1317170203+1014161165*751418916+1341609618*938673626+786325583*1444449623)%2147483647=1812538172
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 6 3 7 0 26%2147483647=1342465241 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1591179681+418714188*309607049+1675147475*546553877+1674326661*1056401817+547797802*1078123924+2073962627*555906257+897270857*681577324+1582958967*2011956623+49892701*1944422173+1256824732*1559246070+1435903714*1425248998+742583315*1033352314+1789294768*1619348998+13407412*982725756+518661610*1657920947+1259751297*1498752791+1695663205*1065449082+2068940067*983776859+940478841*1451701531+1982757556*2000958262+1956713516*1610082924+863066484*1250308965+522298462*1317170203+1343575777*751418916+771712139*938673626+157728743*1444449623)%2147483647=1342465241
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 6 3
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
end AspisR1.JFz_TX2_Q6_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2323092281#u64 3587524865#u64 5005058424#u64 4554109670#u64⟩,⟨pack 2205373470#u64 1272812689#u64 2653266433#u64 3559004982#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 2360280318607672918#u64 3439538283684422993#u64 9070358310830627793#u64 5243208476916381246#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 28941884#u32 1590068101#u32 934607962#u32 1141953134#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 28941884#u32) (JFs_TX2_RawMath.extend 1590068101#u32) (JFs_TX2_RawMath.extend 934607962#u32) (JFs_TX2_RawMath.extend 1141953134#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 28941884#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 28941884#u32) (JFs_TX2_RawMath.extend 1590068101#u32) (JFs_TX2_RawMath.extend 934607962#u32) (JFs_TX2_RawMath.extend 1141953134#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1590068101#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 28941884#u32) (JFs_TX2_RawMath.extend 1590068101#u32) (JFs_TX2_RawMath.extend 934607962#u32) (JFs_TX2_RawMath.extend 1141953134#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 934607962#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 28941884#u32) (JFs_TX2_RawMath.extend 1590068101#u32) (JFs_TX2_RawMath.extend 934607962#u32) (JFs_TX2_RawMath.extend 1141953134#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1141953134#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2645919042522771819#u64 747107088162951345#u64 4962213692959292385#u64 4998262788882649130#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 28941884#u32 1590068101#u32 934607962#u32 1141953134#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 28941884#u32) (JFs_TX2_RawMath.extend 1590068101#u32) (JFs_TX2_RawMath.extend 934607962#u32) (JFs_TX2_RawMath.extend 1141953134#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 28941884#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 28941884#u32) (JFs_TX2_RawMath.extend 1590068101#u32) (JFs_TX2_RawMath.extend 934607962#u32) (JFs_TX2_RawMath.extend 1141953134#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1590068101#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 28941884#u32) (JFs_TX2_RawMath.extend 1590068101#u32) (JFs_TX2_RawMath.extend 934607962#u32) (JFs_TX2_RawMath.extend 1141953134#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 934607962#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 28941884#u32) (JFs_TX2_RawMath.extend 1590068101#u32) (JFs_TX2_RawMath.extend 934607962#u32) (JFs_TX2_RawMath.extend 1141953134#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1141953134#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails16.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value0_3=
      ok (.Ok (pack 28941884#u32 1590068101#u32 934607962#u32 1141953134#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (28941884<2147483647 ∧ 1590068101<2147483647) ∧ (934607962<2147483647 ∧ 1141953134<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 28941884#u32 1590068101#u32 934607962#u32 1141953134#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 28941884#u32 1590068101#u32 934607962#u32 1141953134#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q6_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2323092281#u64 3587524865#u64 5005058424#u64 4554109670#u64⟩,⟨pack 2205373470#u64 1272812689#u64 2653266433#u64 3559004982#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6094643877#u64 4846339607#u64 11190388812#u64 7565344743#u64⟩,⟨pack 5778765935#u64 1655322084#u64 8429686299#u64 4586484359#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 6534521295364603502#u64 532701090324343667#u64 11193575037317514355#u64 3058443885196361725#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1024632685#u32 82614319#u32 427622276#u32 753316840#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1024632685#u32) (JFs_TX2_RawMath.extend 82614319#u32) (JFs_TX2_RawMath.extend 427622276#u32) (JFs_TX2_RawMath.extend 753316840#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1024632685#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1024632685#u32) (JFs_TX2_RawMath.extend 82614319#u32) (JFs_TX2_RawMath.extend 427622276#u32) (JFs_TX2_RawMath.extend 753316840#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 82614319#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1024632685#u32) (JFs_TX2_RawMath.extend 82614319#u32) (JFs_TX2_RawMath.extend 427622276#u32) (JFs_TX2_RawMath.extend 753316840#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 427622276#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1024632685#u32) (JFs_TX2_RawMath.extend 82614319#u32) (JFs_TX2_RawMath.extend 427622276#u32) (JFs_TX2_RawMath.extend 753316840#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 753316840#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5252541081235756992#u64 298881433580139306#u64 9742538695468402036#u64 1210992248198625600#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1024632685#u32 82614319#u32 427622276#u32 753316840#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1024632685#u32) (JFs_TX2_RawMath.extend 82614319#u32) (JFs_TX2_RawMath.extend 427622276#u32) (JFs_TX2_RawMath.extend 753316840#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1024632685#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1024632685#u32) (JFs_TX2_RawMath.extend 82614319#u32) (JFs_TX2_RawMath.extend 427622276#u32) (JFs_TX2_RawMath.extend 753316840#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 82614319#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1024632685#u32) (JFs_TX2_RawMath.extend 82614319#u32) (JFs_TX2_RawMath.extend 427622276#u32) (JFs_TX2_RawMath.extend 753316840#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 427622276#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1024632685#u32) (JFs_TX2_RawMath.extend 82614319#u32) (JFs_TX2_RawMath.extend 427622276#u32) (JFs_TX2_RawMath.extend 753316840#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 753316840#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails16.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value1_3=
      ok (.Ok (pack 1024632685#u32 82614319#u32 427622276#u32 753316840#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1024632685<2147483647 ∧ 82614319<2147483647) ∧ (427622276<2147483647 ∧ 753316840<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1024632685#u32 82614319#u32 427622276#u32 753316840#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2323092281#u64 3587524865#u64 5005058424#u64 4554109670#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1024632685#u32 82614319#u32 427622276#u32 753316840#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2205373470#u64 1272812689#u64 2653266433#u64 3559004982#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q6_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6094643877#u64 4846339607#u64 11190388812#u64 7565344743#u64⟩,⟨pack 5778765935#u64 1655322084#u64 8429686299#u64 4586484359#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9314659463#u64 5933814326#u64 16312790751#u64 9373878311#u64⟩,⟨pack 7900825636#u64 3381684872#u64 13451924907#u64 8425431170#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4202224543727284216#u64 665970712650287732#u64 9370723086262511764#u64 2347475122214156257#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 288048974#u32 989198599#u32 1854860547#u32 523685058#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 288048974#u32) (JFs_TX2_RawMath.extend 989198599#u32) (JFs_TX2_RawMath.extend 1854860547#u32) (JFs_TX2_RawMath.extend 523685058#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 288048974#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 288048974#u32) (JFs_TX2_RawMath.extend 989198599#u32) (JFs_TX2_RawMath.extend 1854860547#u32) (JFs_TX2_RawMath.extend 523685058#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 989198599#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 288048974#u32) (JFs_TX2_RawMath.extend 989198599#u32) (JFs_TX2_RawMath.extend 1854860547#u32) (JFs_TX2_RawMath.extend 523685058#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1854860547#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 288048974#u32) (JFs_TX2_RawMath.extend 989198599#u32) (JFs_TX2_RawMath.extend 1854860547#u32) (JFs_TX2_RawMath.extend 523685058#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 523685058#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3294970917906014854#u64 2288139667929038549#u64 10351083812360579019#u64 6988187897444408895#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 288048974#u32 989198599#u32 1854860547#u32 523685058#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 288048974#u32) (JFs_TX2_RawMath.extend 989198599#u32) (JFs_TX2_RawMath.extend 1854860547#u32) (JFs_TX2_RawMath.extend 523685058#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 288048974#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 288048974#u32) (JFs_TX2_RawMath.extend 989198599#u32) (JFs_TX2_RawMath.extend 1854860547#u32) (JFs_TX2_RawMath.extend 523685058#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 989198599#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 288048974#u32) (JFs_TX2_RawMath.extend 989198599#u32) (JFs_TX2_RawMath.extend 1854860547#u32) (JFs_TX2_RawMath.extend 523685058#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1854860547#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 288048974#u32) (JFs_TX2_RawMath.extend 989198599#u32) (JFs_TX2_RawMath.extend 1854860547#u32) (JFs_TX2_RawMath.extend 523685058#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 523685058#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails16.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value2_3=
      ok (.Ok (pack 288048974#u32 989198599#u32 1854860547#u32 523685058#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (288048974<2147483647 ∧ 989198599<2147483647) ∧ (1854860547<2147483647 ∧ 523685058<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 288048974#u32 989198599#u32 1854860547#u32 523685058#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6094643877#u64 4846339607#u64 11190388812#u64 7565344743#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 288048974#u32 989198599#u32 1854860547#u32 523685058#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5778765935#u64 1655322084#u64 8429686299#u64 4586484359#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q6_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨724724875#u32,1638847032#u32⟩,⟨1280405222#u32,783943723#u32⟩⟩,⟨⟨1458374695#u32,1234201225#u32⟩,⟨567023025#u32,1982980229#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q6_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q6_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9314659463%2147483647 at h0
  norm_num at h0
  have e0 : a0=724724875#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5933814326%2147483647 at h1
  norm_num at h1
  have e1 : a1=1638847032#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16312790751%2147483647 at h2
  norm_num at h2
  have e2 : a2=1280405222#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9373878311%2147483647 at h3
  norm_num at h3
  have e3 : a3=783943723#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=7900825636%2147483647 at h4
  norm_num at h4
  have e4 : a4=1458374695#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=3381684872%2147483647 at h5
  norm_num at h5
  have e5 : a5=1234201225#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=13451924907%2147483647 at h6
  norm_num at h6
  have e6 : a6=567023025#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=8425431170%2147483647 at h7
  norm_num at h7
  have e7 : a7=1982980229#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q6_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails16.value0_3
      from JFr_TX2_Tails16.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails16.value1_3
      from JFr_TX2_Tails16.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails16.value2_3
      from JFr_TX2_Tails16.source2_3,
    JFz_TX2_Q6_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q6_Raw30.after=JFz_TX2_Q6_Raw31.before := rfl
  have same2 : JFz_TX2_Q6_Raw31.after=JFz_TX2_Q6_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q6_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q6_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q6_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1934323592#u32,1569267507#u32⟩,⟨1871247934#u32,915919120#u32⟩⟩,⟨⟨1602534631#u32,2011641507#u32⟩,⟨232077550#u32,1177961823#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1934323592<2147483647 ∧ 1569267507<2147483647) ∧ (1871247934<2147483647 ∧ 915919120<2147483647)) ∧
    ((1602534631<2147483647 ∧ 2011641507<2147483647) ∧ (232077550<2147483647 ∧ 1177961823<2147483647))
  omega
theorem addition : decode JFz_TX2_Q6_Head3.value+decode JFz_TX2_Q6_Tail3.value=decode value := by
  change (⟨⟨⟨1209598717,2077904122⟩,⟨590842712,131975397⟩⟩,⟨⟨144159936,777440282⟩,⟨1812538172,1342465241⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨724724875,1638847032⟩,⟨1280405222,783943723⟩⟩,⟨⟨1458374695,1234201225⟩,⟨567023025,1982980229⟩⟩⟩=⟨⟨⟨1934323592,1569267507⟩,⟨1871247934,915919120⟩⟩,⟨⟨1602534631,2011641507⟩,⟨232077550,1177961823⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 6 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q6_Head3.value JFz_TX2_Q6_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q6_Head3.source,
      JFz_TX2_Q6_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q6_Head3.value := by
    change ((1209598717<2147483647 ∧ 2077904122<2147483647) ∧ (590842712<2147483647 ∧ 131975397<2147483647)) ∧
      ((144159936<2147483647 ∧ 777440282<2147483647) ∧ (1812538172<2147483647 ∧ 1342465241<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q6_Tail3.value := by
    change ((724724875<2147483647 ∧ 1638847032<2147483647) ∧ (1280405222<2147483647 ∧ 783943723<2147483647)) ∧
      ((1458374695<2147483647 ∧ 1234201225<2147483647) ∧ (567023025<2147483647 ∧ 1982980229<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q6_Dot3
end
