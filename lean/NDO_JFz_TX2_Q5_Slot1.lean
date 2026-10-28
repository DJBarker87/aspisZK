import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails15
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1400740297#u32,1203685700#u32⟩,⟨33690483#u32,891906739#u32⟩⟩,⟨⟨1122887046#u32,1753588095#u32⟩,⟨1277432754#u32,2077368633#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 5 1 0 0 26%2147483647=1400740297 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1426719968+855639275*231085188+867568255*619415045+352063*1299325630+1106523000*294197736+1554033304*1637288753+1430280692*913684166+1491718280*193041370+118514350*631106478+1675652887*1063306116+1364884909*306995662+1135303194*862099334+304762092*658132775+1465393816*513058796+824208172*1144627658+1752653420*1210058087+1385409049*668191489+1003904973*680379868+1298953245*15931656+2005758375*521682391+497936241*1407705699+235809508*455624210+1478307182*1319582921+1858903615*1870062224+628035096*112491200+1244951250*1703907727)%2147483647=1400740297
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 5 1 1 0 26%2147483647=1203685700 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1426719968+1483149559*231085188+655227887*619415045+39062738*1299325630+729079828*294197736+67370206*1637288753+1685049618*913684166+385547620*193041370+1786803209*631106478+779721715*1063306116+594709522*306995662+338788461*862099334+526756808*658132775+184076238*513058796+1852498770*1144627658+2102463508*1210058087+1086671526*668191489+1147694576*680379868+1504805752*15931656+2005073905*521682391+185008025*1407705699+1485990146*455624210+1255280192*1319582921+1018329259*1870062224+570157693*112491200+1511904630*1703907727)%2147483647=1203685700
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 5 1 2 0 26%2147483647=33690483 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1426719968+1898717401*231085188+1032732628*619415045+1313565596*1299325630+1074182998*294197736+1410213748*1637288753+1182702806*913684166+321711020*193041370+2062791928*631106478+1188803754*1063306116+2038502201*306995662+735931834*862099334+1330533011*658132775+1052874750*513058796+950153811*1144627658+1225424092*1210058087+1659116453*668191489+1474177753*680379868+2073609211*15931656+1602919019*521682391+1865917845*1407705699+1085624123*455624210+1837870964*1319582921+1550509101*1870062224+1661725734*112491200+2066655336*1703907727)%2147483647=33690483
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 5 1 3 0 26%2147483647=891906739 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1426719968+1849775942*231085188+656039795*619415045+1840648083*1299325630+246996287*294197736+1369248953*1637288753+1132591724*913684166+92744917*193041370+1719480363*631106478+1266677922*1063306116+377386917*306995662+735227219*862099334+465096431*658132775+451889791*513058796+1379836302*1144627658+618598847*1210058087+1624084534*668191489+1511477847*680379868+1840812326*15931656+185546252*521682391+2145463598*1407705699+82870699*455624210+1625323762*1319582921+1843639311*1870062224+1777269271*112491200+1645120956*1703907727)%2147483647=891906739
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 5 1 4 0 26%2147483647=1122887046 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1426719968+1112406525*231085188+1345999435*619415045+752376469*1299325630+634588140*294197736+1419170319*1637288753+1702860885*913684166+710076517*193041370+1256487405*631106478+1114745059*1063306116+1137838899*306995662+1254184109*862099334+1038210451*658132775+274378589*513058796+171986381*1144627658+1536678585*1210058087+1305878831*668191489+1335902916*680379868+1755193245*15931656+2023391453*521682391+293456010*1407705699+1751078325*455624210+1423042536*1319582921+1749638204*1870062224+1345811362*112491200+1284924881*1703907727)%2147483647=1122887046
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 5 1 5 0 26%2147483647=1753588095 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1426719968+1796814865*231085188+1253123171*619415045+1317611639*1299325630+1559245386*294197736+1866942376*1637288753+1973593402*913684166+47019780*193041370+1353487525*631106478+1840161555*1063306116+2003659556*306995662+200559114*862099334+334988447*658132775+2023650872*513058796+1296497964*1144627658+34285357*1210058087+1685894190*668191489+995962325*680379868+1295624230*15931656+1199631211*521682391+1948677857*1407705699+1425322328*455624210+1466877680*1319582921+702011012*1870062224+937706871*112491200+455802666*1703907727)%2147483647=1753588095
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 5 1 6 0 26%2147483647=1277432754 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1426719968+1838939499*231085188+1353876630*619415045+1258713036*1299325630+1947503436*294197736+1271796599*1637288753+1660157177*913684166+564707688*193041370+1858113864*631106478+1015817431*1063306116+1264608004*306995662+735383960*862099334+221696734*658132775+1297524163*513058796+109088572*1144627658+792206628*1210058087+1921581249*668191489+94118806*680379868+476103426*15931656+239612482*521682391+177052717*1407705699+826458039*455624210+1923715623*1319582921+1014161165*1870062224+1341609618*112491200+786325583*1703907727)%2147483647=1277432754
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 5 1 7 0 26%2147483647=2077368633 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1426719968+418714188*231085188+1675147475*619415045+1674326661*1299325630+547797802*294197736+2073962627*1637288753+897270857*913684166+1582958967*193041370+49892701*631106478+1256824732*1063306116+1435903714*306995662+742583315*862099334+1789294768*658132775+13407412*513058796+518661610*1144627658+1259751297*1210058087+1695663205*668191489+2068940067*680379868+940478841*15931656+1982757556*521682391+1956713516*1407705699+863066484*455624210+522298462*1319582921+1343575777*1870062224+771712139*112491200+157728743*1703907727)%2147483647=2077368633
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 5 1
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
end AspisR1.JFz_TX2_Q5_Head1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw10
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4191235047#u64 3386637232#u64 6516584100#u64 3755790342#u64⟩,⟨pack 3329093970#u64 1920766923#u64 5754986151#u64 4108875140#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 7514620136351765889#u64 3473660602485973981#u64 13237995545655349509#u64 4691911750627542597#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1684594819#u32 478736971#u32 1656253808#u32 610877800#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1684594819#u32) (JFs_TX2_RawMath.extend 478736971#u32) (JFs_TX2_RawMath.extend 1656253808#u32) (JFs_TX2_RawMath.extend 610877800#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1684594819#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1684594819#u32) (JFs_TX2_RawMath.extend 478736971#u32) (JFs_TX2_RawMath.extend 1656253808#u32) (JFs_TX2_RawMath.extend 610877800#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 478736971#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1684594819#u32) (JFs_TX2_RawMath.extend 478736971#u32) (JFs_TX2_RawMath.extend 1656253808#u32) (JFs_TX2_RawMath.extend 610877800#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1656253808#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1684594819#u32) (JFs_TX2_RawMath.extend 478736971#u32) (JFs_TX2_RawMath.extend 1656253808#u32) (JFs_TX2_RawMath.extend 610877800#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 610877800#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4769301301287584971#u64 2310435854811394421#u64 11663245767221298737#u64 6831715064451052597#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1684594819#u32 478736971#u32 1656253808#u32 610877800#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1684594819#u32) (JFs_TX2_RawMath.extend 478736971#u32) (JFs_TX2_RawMath.extend 1656253808#u32) (JFs_TX2_RawMath.extend 610877800#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1684594819#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1684594819#u32) (JFs_TX2_RawMath.extend 478736971#u32) (JFs_TX2_RawMath.extend 1656253808#u32) (JFs_TX2_RawMath.extend 610877800#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 478736971#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1684594819#u32) (JFs_TX2_RawMath.extend 478736971#u32) (JFs_TX2_RawMath.extend 1656253808#u32) (JFs_TX2_RawMath.extend 610877800#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1656253808#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1684594819#u32) (JFs_TX2_RawMath.extend 478736971#u32) (JFs_TX2_RawMath.extend 1656253808#u32) (JFs_TX2_RawMath.extend 610877800#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 610877800#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails15.value0_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value0_1=
      ok (.Ok (pack 1684594819#u32 478736971#u32 1656253808#u32 610877800#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1684594819<2147483647 ∧ 478736971<2147483647) ∧ (1656253808<2147483647 ∧ 610877800<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1684594819#u32 478736971#u32 1656253808#u32 610877800#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1684594819#u32 478736971#u32 1656253808#u32 610877800#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q5_Raw10
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4191235047#u64 3386637232#u64 6516584100#u64 3755790342#u64⟩,⟨pack 3329093970#u64 1920766923#u64 5754986151#u64 4108875140#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6493456974#u64 6312119456#u64 10918361148#u64 7702725837#u64⟩,⟨pack 7318619682#u64 4050661488#u64 11128211755#u64 6551506013#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 4684240368503723727#u64 2280031284125677618#u64 8393473773237866942#u64 5014000292465137505#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 258333201#u32 1146522666#u32 430513231#u32 1466730327#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 258333201#u32) (JFs_TX2_RawMath.extend 1146522666#u32) (JFs_TX2_RawMath.extend 430513231#u32) (JFs_TX2_RawMath.extend 1466730327#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 258333201#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 258333201#u32) (JFs_TX2_RawMath.extend 1146522666#u32) (JFs_TX2_RawMath.extend 430513231#u32) (JFs_TX2_RawMath.extend 1466730327#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1146522666#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 258333201#u32) (JFs_TX2_RawMath.extend 1146522666#u32) (JFs_TX2_RawMath.extend 430513231#u32) (JFs_TX2_RawMath.extend 1466730327#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 430513231#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 258333201#u32) (JFs_TX2_RawMath.extend 1146522666#u32) (JFs_TX2_RawMath.extend 430513231#u32) (JFs_TX2_RawMath.extend 1466730327#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1466730327#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4503421205584058717#u64 801174982732737496#u64 8613819512085548058#u64 1723568889318663502#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 258333201#u32 1146522666#u32 430513231#u32 1466730327#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 258333201#u32) (JFs_TX2_RawMath.extend 1146522666#u32) (JFs_TX2_RawMath.extend 430513231#u32) (JFs_TX2_RawMath.extend 1466730327#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 258333201#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 258333201#u32) (JFs_TX2_RawMath.extend 1146522666#u32) (JFs_TX2_RawMath.extend 430513231#u32) (JFs_TX2_RawMath.extend 1466730327#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1146522666#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 258333201#u32) (JFs_TX2_RawMath.extend 1146522666#u32) (JFs_TX2_RawMath.extend 430513231#u32) (JFs_TX2_RawMath.extend 1466730327#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 430513231#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 258333201#u32) (JFs_TX2_RawMath.extend 1146522666#u32) (JFs_TX2_RawMath.extend 430513231#u32) (JFs_TX2_RawMath.extend 1466730327#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1466730327#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails15.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value1_1=
      ok (.Ok (pack 258333201#u32 1146522666#u32 430513231#u32 1466730327#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (258333201<2147483647 ∧ 1146522666<2147483647) ∧ (430513231<2147483647 ∧ 1466730327<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 258333201#u32 1146522666#u32 430513231#u32 1466730327#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4191235047#u64 3386637232#u64 6516584100#u64 3755790342#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 258333201#u32 1146522666#u32 430513231#u32 1466730327#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3329093970#u64 1920766923#u64 5754986151#u64 4108875140#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q5_Raw11
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw12
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6493456974#u64 6312119456#u64 10918361148#u64 7702725837#u64⟩,⟨pack 7318619682#u64 4050661488#u64 11128211755#u64 6551506013#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9746726842#u64 7965653287#u64 16833042989#u64 8691784147#u64⟩,⟨pack 9581910185#u64 7038332673#u64 14599007298#u64 9396157795#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4490533841949543411#u64 722353190573591483#u64 8565857438908730888#u64 1677102265924013510#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 598238100#u32 757530410#u32 66652649#u32 1102098207#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 598238100#u32) (JFs_TX2_RawMath.extend 757530410#u32) (JFs_TX2_RawMath.extend 66652649#u32) (JFs_TX2_RawMath.extend 1102098207#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 598238100#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 598238100#u32) (JFs_TX2_RawMath.extend 757530410#u32) (JFs_TX2_RawMath.extend 66652649#u32) (JFs_TX2_RawMath.extend 1102098207#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 757530410#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 598238100#u32) (JFs_TX2_RawMath.extend 757530410#u32) (JFs_TX2_RawMath.extend 66652649#u32) (JFs_TX2_RawMath.extend 1102098207#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 66652649#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 598238100#u32) (JFs_TX2_RawMath.extend 757530410#u32) (JFs_TX2_RawMath.extend 66652649#u32) (JFs_TX2_RawMath.extend 1102098207#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1102098207#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4273673724592966479#u64 2450145433940584957#u64 7191675624183051606#u64 4785028575533089984#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 598238100#u32 757530410#u32 66652649#u32 1102098207#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 598238100#u32) (JFs_TX2_RawMath.extend 757530410#u32) (JFs_TX2_RawMath.extend 66652649#u32) (JFs_TX2_RawMath.extend 1102098207#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 598238100#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 598238100#u32) (JFs_TX2_RawMath.extend 757530410#u32) (JFs_TX2_RawMath.extend 66652649#u32) (JFs_TX2_RawMath.extend 1102098207#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 757530410#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 598238100#u32) (JFs_TX2_RawMath.extend 757530410#u32) (JFs_TX2_RawMath.extend 66652649#u32) (JFs_TX2_RawMath.extend 1102098207#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 66652649#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 598238100#u32) (JFs_TX2_RawMath.extend 757530410#u32) (JFs_TX2_RawMath.extend 66652649#u32) (JFs_TX2_RawMath.extend 1102098207#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1102098207#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails15.value2_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value2_1=
      ok (.Ok (pack 598238100#u32 757530410#u32 66652649#u32 1102098207#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (598238100<2147483647 ∧ 757530410<2147483647) ∧ (66652649<2147483647 ∧ 1102098207<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 598238100#u32 757530410#u32 66652649#u32 1102098207#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6493456974#u64 6312119456#u64 10918361148#u64 7702725837#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 598238100#u32 757530410#u32 66652649#u32 1102098207#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7318619682#u64 4050661488#u64 11128211755#u64 6551506013#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q5_Raw12
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Tail1
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1156792254#u32,1523202346#u32⟩,⟨1800657460#u32,101849559#u32⟩⟩,⟨⟨991975597#u32,595881732#u32⟩,⟨1714105416#u32,806223207#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q5_Raw12.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q5_Raw12.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9746726842%2147483647 at h0
  norm_num at h0
  have e0 : a0=1156792254#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7965653287%2147483647 at h1
  norm_num at h1
  have e1 : a1=1523202346#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16833042989%2147483647 at h2
  norm_num at h2
  have e2 : a2=1800657460#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8691784147%2147483647 at h3
  norm_num at h3
  have e3 : a3=101849559#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9581910185%2147483647 at h4
  norm_num at h4
  have e4 : a4=991975597#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=7038332673%2147483647 at h5
  norm_num at h5
  have e5 : a5=595881732#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14599007298%2147483647 at h6
  norm_num at h6
  have e6 : a6=1714105416#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=9396157795%2147483647 at h7
  norm_num at h7
  have e7 : a7=806223207#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q5_Raw10.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JFr_TX2_Tails15.value0_1
      from JFr_TX2_Tails15.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JFr_TX2_Tails15.value1_1
      from JFr_TX2_Tails15.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JFr_TX2_Tails15.value2_1
      from JFr_TX2_Tails15.source2_1,
    JFz_TX2_Q5_Raw10.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q5_Raw10.after=JFz_TX2_Q5_Raw11.before := rfl
  have same2 : JFz_TX2_Q5_Raw11.after=JFz_TX2_Q5_Raw12.before := rfl
  simp only [same1,JFz_TX2_Q5_Raw11.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q5_Raw12.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q5_Tail1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨410048904#u32,579404399#u32⟩,⟨1834347943#u32,993756298#u32⟩⟩,⟨⟨2114862643#u32,201986180#u32⟩,⟨844054523#u32,736108193#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((410048904<2147483647 ∧ 579404399<2147483647) ∧ (1834347943<2147483647 ∧ 993756298<2147483647)) ∧
    ((2114862643<2147483647 ∧ 201986180<2147483647) ∧ (844054523<2147483647 ∧ 736108193<2147483647))
  omega
theorem addition : decode JFz_TX2_Q5_Head1.value+decode JFz_TX2_Q5_Tail1.value=decode value := by
  change (⟨⟨⟨1400740297,1203685700⟩,⟨33690483,891906739⟩⟩,⟨⟨1122887046,1753588095⟩,⟨1277432754,2077368633⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1156792254,1523202346⟩,⟨1800657460,101849559⟩⟩,⟨⟨991975597,595881732⟩,⟨1714105416,806223207⟩⟩⟩=⟨⟨⟨410048904,579404399⟩,⟨1834347943,993756298⟩⟩,⟨⟨2114862643,201986180⟩,⟨844054523,736108193⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 5 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q5_Head1.value JFz_TX2_Q5_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q5_Head1.source,
      JFz_TX2_Q5_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q5_Head1.value := by
    change ((1400740297<2147483647 ∧ 1203685700<2147483647) ∧ (33690483<2147483647 ∧ 891906739<2147483647)) ∧
      ((1122887046<2147483647 ∧ 1753588095<2147483647) ∧ (1277432754<2147483647 ∧ 2077368633<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q5_Tail1.value := by
    change ((1156792254<2147483647 ∧ 1523202346<2147483647) ∧ (1800657460<2147483647 ∧ 101849559<2147483647)) ∧
      ((991975597<2147483647 ∧ 595881732<2147483647) ∧ (1714105416<2147483647 ∧ 806223207<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q5_Dot1
end
