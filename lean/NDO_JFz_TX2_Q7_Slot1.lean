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
namespace AspisR1.JFz_TX2_Q7_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1306622708#u32,68922493#u32⟩,⟨1967428521#u32,1176805225#u32⟩⟩,⟨⟨913428815#u32,1426119533#u32⟩,⟨1253869526#u32,173459399#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 7 1 0 0 26%2147483647=1306622708 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*980186315+855639275*844153745+867568255*1142481333+352063*1859117232+1106523000*1944163534+1554033304*2050617995+1430280692*338192969+1491718280*651511572+118514350*1072562022+1675652887*915616083+1364884909*1994389070+1135303194*1935090119+304762092*331960957+1465393816*122940927+824208172*1371247138+1752653420*2063960706+1385409049*722178649+1003904973*1207630335+1298953245*274474557+2005758375*1658256575+497936241*373098714+235809508*1676542654+1478307182*892391505+1858903615*1973279790+628035096*1420290868+1244951250*1700251879)%2147483647=1306622708
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 7 1 1 0 26%2147483647=68922493 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*980186315+1483149559*844153745+655227887*1142481333+39062738*1859117232+729079828*1944163534+67370206*2050617995+1685049618*338192969+385547620*651511572+1786803209*1072562022+779721715*915616083+594709522*1994389070+338788461*1935090119+526756808*331960957+184076238*122940927+1852498770*1371247138+2102463508*2063960706+1086671526*722178649+1147694576*1207630335+1504805752*274474557+2005073905*1658256575+185008025*373098714+1485990146*1676542654+1255280192*892391505+1018329259*1973279790+570157693*1420290868+1511904630*1700251879)%2147483647=68922493
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 7 1 2 0 26%2147483647=1967428521 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*980186315+1898717401*844153745+1032732628*1142481333+1313565596*1859117232+1074182998*1944163534+1410213748*2050617995+1182702806*338192969+321711020*651511572+2062791928*1072562022+1188803754*915616083+2038502201*1994389070+735931834*1935090119+1330533011*331960957+1052874750*122940927+950153811*1371247138+1225424092*2063960706+1659116453*722178649+1474177753*1207630335+2073609211*274474557+1602919019*1658256575+1865917845*373098714+1085624123*1676542654+1837870964*892391505+1550509101*1973279790+1661725734*1420290868+2066655336*1700251879)%2147483647=1967428521
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 7 1 3 0 26%2147483647=1176805225 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*980186315+1849775942*844153745+656039795*1142481333+1840648083*1859117232+246996287*1944163534+1369248953*2050617995+1132591724*338192969+92744917*651511572+1719480363*1072562022+1266677922*915616083+377386917*1994389070+735227219*1935090119+465096431*331960957+451889791*122940927+1379836302*1371247138+618598847*2063960706+1624084534*722178649+1511477847*1207630335+1840812326*274474557+185546252*1658256575+2145463598*373098714+82870699*1676542654+1625323762*892391505+1843639311*1973279790+1777269271*1420290868+1645120956*1700251879)%2147483647=1176805225
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 7 1 4 0 26%2147483647=913428815 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*980186315+1112406525*844153745+1345999435*1142481333+752376469*1859117232+634588140*1944163534+1419170319*2050617995+1702860885*338192969+710076517*651511572+1256487405*1072562022+1114745059*915616083+1137838899*1994389070+1254184109*1935090119+1038210451*331960957+274378589*122940927+171986381*1371247138+1536678585*2063960706+1305878831*722178649+1335902916*1207630335+1755193245*274474557+2023391453*1658256575+293456010*373098714+1751078325*1676542654+1423042536*892391505+1749638204*1973279790+1345811362*1420290868+1284924881*1700251879)%2147483647=913428815
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 7 1 5 0 26%2147483647=1426119533 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*980186315+1796814865*844153745+1253123171*1142481333+1317611639*1859117232+1559245386*1944163534+1866942376*2050617995+1973593402*338192969+47019780*651511572+1353487525*1072562022+1840161555*915616083+2003659556*1994389070+200559114*1935090119+334988447*331960957+2023650872*122940927+1296497964*1371247138+34285357*2063960706+1685894190*722178649+995962325*1207630335+1295624230*274474557+1199631211*1658256575+1948677857*373098714+1425322328*1676542654+1466877680*892391505+702011012*1973279790+937706871*1420290868+455802666*1700251879)%2147483647=1426119533
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 7 1 6 0 26%2147483647=1253869526 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*980186315+1838939499*844153745+1353876630*1142481333+1258713036*1859117232+1947503436*1944163534+1271796599*2050617995+1660157177*338192969+564707688*651511572+1858113864*1072562022+1015817431*915616083+1264608004*1994389070+735383960*1935090119+221696734*331960957+1297524163*122940927+109088572*1371247138+792206628*2063960706+1921581249*722178649+94118806*1207630335+476103426*274474557+239612482*1658256575+177052717*373098714+826458039*1676542654+1923715623*892391505+1014161165*1973279790+1341609618*1420290868+786325583*1700251879)%2147483647=1253869526
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 7 1 7 0 26%2147483647=173459399 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*980186315+418714188*844153745+1675147475*1142481333+1674326661*1859117232+547797802*1944163534+2073962627*2050617995+897270857*338192969+1582958967*651511572+49892701*1072562022+1256824732*915616083+1435903714*1994389070+742583315*1935090119+1789294768*331960957+13407412*122940927+518661610*1371247138+1259751297*2063960706+1695663205*722178649+2068940067*1207630335+940478841*274474557+1982757556*1658256575+1956713516*373098714+863066484*1676542654+522298462*892391505+1343575777*1973279790+771712139*1420290868+157728743*1700251879)%2147483647=173459399
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 7 1
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
end AspisR1.JFz_TX2_Q7_Head1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw10
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5110297652#u64 1884506299#u64 6827246924#u64 2906259286#u64⟩,⟨pack 4283817074#u64 930995627#u64 5381388369#u64 4240189040#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 6540685384371574477#u64 2055463579473565251#u64 11423628630280749535#u64 4848470845311912511#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1064375086#u32 237287093#u32 1355179855#u32 1085039480#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1064375086#u32) (JFs_TX2_RawMath.extend 237287093#u32) (JFs_TX2_RawMath.extend 1355179855#u32) (JFs_TX2_RawMath.extend 1085039480#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1064375086#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1064375086#u32) (JFs_TX2_RawMath.extend 237287093#u32) (JFs_TX2_RawMath.extend 1355179855#u32) (JFs_TX2_RawMath.extend 1085039480#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 237287093#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1064375086#u32) (JFs_TX2_RawMath.extend 237287093#u32) (JFs_TX2_RawMath.extend 1355179855#u32) (JFs_TX2_RawMath.extend 1085039480#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1355179855#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1064375086#u32) (JFs_TX2_RawMath.extend 237287093#u32) (JFs_TX2_RawMath.extend 1355179855#u32) (JFs_TX2_RawMath.extend 1085039480#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1085039480#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4792398708636504571#u64 1430644668735456813#u64 10169092991772375020#u64 4879438694706947881#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1064375086#u32 237287093#u32 1355179855#u32 1085039480#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1064375086#u32) (JFs_TX2_RawMath.extend 237287093#u32) (JFs_TX2_RawMath.extend 1355179855#u32) (JFs_TX2_RawMath.extend 1085039480#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1064375086#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1064375086#u32) (JFs_TX2_RawMath.extend 237287093#u32) (JFs_TX2_RawMath.extend 1355179855#u32) (JFs_TX2_RawMath.extend 1085039480#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 237287093#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1064375086#u32) (JFs_TX2_RawMath.extend 237287093#u32) (JFs_TX2_RawMath.extend 1355179855#u32) (JFs_TX2_RawMath.extend 1085039480#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1355179855#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1064375086#u32) (JFs_TX2_RawMath.extend 237287093#u32) (JFs_TX2_RawMath.extend 1355179855#u32) (JFs_TX2_RawMath.extend 1085039480#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1085039480#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails17.value0_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value0_1=
      ok (.Ok (pack 1064375086#u32 237287093#u32 1355179855#u32 1085039480#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1064375086<2147483647 ∧ 237287093<2147483647) ∧ (1355179855<2147483647 ∧ 1085039480<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1064375086#u32 237287093#u32 1355179855#u32 1085039480#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1064375086#u32 237287093#u32 1355179855#u32 1085039480#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q7_Raw10
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5110297652#u64 1884506299#u64 6827246924#u64 2906259286#u64⟩,⟨pack 4283817074#u64 930995627#u64 5381388369#u64 4240189040#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9038125935#u64 3254178985#u64 13768734157#u64 7214124373#u64⟩,⟨pack 8427146383#u64 2864475774#u64 11332878486#u64 5808917617#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 7093532501678445255#u64 1214110040461461154#u64 10906566891636448999#u64 6041620537025004099#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1373697356#u32 373033934#u32 412675674#u32 1852542195#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1373697356#u32) (JFs_TX2_RawMath.extend 373033934#u32) (JFs_TX2_RawMath.extend 412675674#u32) (JFs_TX2_RawMath.extend 1852542195#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1373697356#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1373697356#u32) (JFs_TX2_RawMath.extend 373033934#u32) (JFs_TX2_RawMath.extend 412675674#u32) (JFs_TX2_RawMath.extend 1852542195#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 373033934#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1373697356#u32) (JFs_TX2_RawMath.extend 373033934#u32) (JFs_TX2_RawMath.extend 412675674#u32) (JFs_TX2_RawMath.extend 1852542195#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 412675674#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1373697356#u32) (JFs_TX2_RawMath.extend 373033934#u32) (JFs_TX2_RawMath.extend 412675674#u32) (JFs_TX2_RawMath.extend 1852542195#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1852542195#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5407993359972963712#u64 569810954891415741#u64 9464175096450876943#u64 2248929232012266384#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1373697356#u32 373033934#u32 412675674#u32 1852542195#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1373697356#u32) (JFs_TX2_RawMath.extend 373033934#u32) (JFs_TX2_RawMath.extend 412675674#u32) (JFs_TX2_RawMath.extend 1852542195#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1373697356#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1373697356#u32) (JFs_TX2_RawMath.extend 373033934#u32) (JFs_TX2_RawMath.extend 412675674#u32) (JFs_TX2_RawMath.extend 1852542195#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 373033934#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1373697356#u32) (JFs_TX2_RawMath.extend 373033934#u32) (JFs_TX2_RawMath.extend 412675674#u32) (JFs_TX2_RawMath.extend 1852542195#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 412675674#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1373697356#u32) (JFs_TX2_RawMath.extend 373033934#u32) (JFs_TX2_RawMath.extend 412675674#u32) (JFs_TX2_RawMath.extend 1852542195#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1852542195#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails17.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value1_1=
      ok (.Ok (pack 1373697356#u32 373033934#u32 412675674#u32 1852542195#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1373697356<2147483647 ∧ 373033934<2147483647) ∧ (412675674<2147483647 ∧ 1852542195<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1373697356#u32 373033934#u32 412675674#u32 1852542195#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5110297652#u64 1884506299#u64 6827246924#u64 2906259286#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1373697356#u32 373033934#u32 412675674#u32 1852542195#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4283817074#u64 930995627#u64 5381388369#u64 4240189040#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q7_Raw11
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Raw12
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9038125935#u64 3254178985#u64 13768734157#u64 7214124373#u64⟩,⟨pack 8427146383#u64 2864475774#u64 11332878486#u64 5808917617#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 12896618894#u64 4650607667#u64 19646403065#u64 10500894569#u64⟩,⟨pack 13064248017#u64 6226486253#u64 16975172348#u64 9504255907#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4915617617614233028#u64 1715717273594685440#u64 10133853732661673886#u64 2759403650153538581#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1944510838#u32 1221428567#u32 466900112#u32 45279207#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1944510838#u32) (JFs_TX2_RawMath.extend 1221428567#u32) (JFs_TX2_RawMath.extend 466900112#u32) (JFs_TX2_RawMath.extend 45279207#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1944510838#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1944510838#u32) (JFs_TX2_RawMath.extend 1221428567#u32) (JFs_TX2_RawMath.extend 466900112#u32) (JFs_TX2_RawMath.extend 45279207#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1221428567#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1944510838#u32) (JFs_TX2_RawMath.extend 1221428567#u32) (JFs_TX2_RawMath.extend 466900112#u32) (JFs_TX2_RawMath.extend 45279207#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 466900112#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1944510838#u32) (JFs_TX2_RawMath.extend 1221428567#u32) (JFs_TX2_RawMath.extend 466900112#u32) (JFs_TX2_RawMath.extend 45279207#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 45279207#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5806050873440081215#u64 5761433063992771518#u64 11869910219529767293#u64 7098312278205651041#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1944510838#u32 1221428567#u32 466900112#u32 45279207#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1944510838#u32) (JFs_TX2_RawMath.extend 1221428567#u32) (JFs_TX2_RawMath.extend 466900112#u32) (JFs_TX2_RawMath.extend 45279207#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1944510838#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1944510838#u32) (JFs_TX2_RawMath.extend 1221428567#u32) (JFs_TX2_RawMath.extend 466900112#u32) (JFs_TX2_RawMath.extend 45279207#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1221428567#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1944510838#u32) (JFs_TX2_RawMath.extend 1221428567#u32) (JFs_TX2_RawMath.extend 466900112#u32) (JFs_TX2_RawMath.extend 45279207#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 466900112#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1944510838#u32) (JFs_TX2_RawMath.extend 1221428567#u32) (JFs_TX2_RawMath.extend 466900112#u32) (JFs_TX2_RawMath.extend 45279207#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 45279207#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails17.value2_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails17.value2_1=
      ok (.Ok (pack 1944510838#u32 1221428567#u32 466900112#u32 45279207#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1944510838<2147483647 ∧ 1221428567<2147483647) ∧ (466900112<2147483647 ∧ 45279207<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1944510838#u32 1221428567#u32 466900112#u32 45279207#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 9038125935#u64 3254178985#u64 13768734157#u64 7214124373#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1944510838#u32 1221428567#u32 466900112#u32 45279207#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 8427146383#u64 2864475774#u64 11332878486#u64 5808917617#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q7_Raw12
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Tail1
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨11717012#u32,355640373#u32⟩,⟨319050242#u32,1910959981#u32⟩⟩,⟨⟨179346135#u32,1931518959#u32⟩,⟨1942786819#u32,914321319#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q7_Raw12.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q7_Raw12.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=12896618894%2147483647 at h0
  norm_num at h0
  have e0 : a0=11717012#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=4650607667%2147483647 at h1
  norm_num at h1
  have e1 : a1=355640373#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=19646403065%2147483647 at h2
  norm_num at h2
  have e2 : a2=319050242#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10500894569%2147483647 at h3
  norm_num at h3
  have e3 : a3=1910959981#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=13064248017%2147483647 at h4
  norm_num at h4
  have e4 : a4=179346135#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=6226486253%2147483647 at h5
  norm_num at h5
  have e5 : a5=1931518959#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16975172348%2147483647 at h6
  norm_num at h6
  have e6 : a6=1942786819#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=9504255907%2147483647 at h7
  norm_num at h7
  have e7 : a7=914321319#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q7_Raw10.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JFr_TX2_Tails17.value0_1
      from JFr_TX2_Tails17.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JFr_TX2_Tails17.value1_1
      from JFr_TX2_Tails17.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 7))
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JFr_TX2_Tails17.value2_1
      from JFr_TX2_Tails17.source2_1,
    JFz_TX2_Q7_Raw10.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q7_Raw10.after=JFz_TX2_Q7_Raw11.before := rfl
  have same2 : JFz_TX2_Q7_Raw11.after=JFz_TX2_Q7_Raw12.before := rfl
  simp only [same1,JFz_TX2_Q7_Raw11.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q7_Raw12.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q7_Tail1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q7_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1318339720#u32,424562866#u32⟩,⟨138995116#u32,940281559#u32⟩⟩,⟨⟨1092774950#u32,1210154845#u32⟩,⟨1049172698#u32,1087780718#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1318339720<2147483647 ∧ 424562866<2147483647) ∧ (138995116<2147483647 ∧ 940281559<2147483647)) ∧
    ((1092774950<2147483647 ∧ 1210154845<2147483647) ∧ (1049172698<2147483647 ∧ 1087780718<2147483647))
  omega
theorem addition : decode JFz_TX2_Q7_Head1.value+decode JFz_TX2_Q7_Tail1.value=decode value := by
  change (⟨⟨⟨1306622708,68922493⟩,⟨1967428521,1176805225⟩⟩,⟨⟨913428815,1426119533⟩,⟨1253869526,173459399⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨11717012,355640373⟩,⟨319050242,1910959981⟩⟩,⟨⟨179346135,1931518959⟩,⟨1942786819,914321319⟩⟩⟩=⟨⟨⟨1318339720,424562866⟩,⟨138995116,940281559⟩⟩,⟨⟨1092774950,1210154845⟩,⟨1049172698,1087780718⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 7)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 7 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q7_Head1.value JFz_TX2_Q7_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q7_Head1.source,
      JFz_TX2_Q7_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q7_Head1.value := by
    change ((1306622708<2147483647 ∧ 68922493<2147483647) ∧ (1967428521<2147483647 ∧ 1176805225<2147483647)) ∧
      ((913428815<2147483647 ∧ 1426119533<2147483647) ∧ (1253869526<2147483647 ∧ 173459399<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q7_Tail1.value := by
    change ((11717012<2147483647 ∧ 355640373<2147483647) ∧ (319050242<2147483647 ∧ 1910959981<2147483647)) ∧
      ((179346135<2147483647 ∧ 1931518959<2147483647) ∧ (1942786819<2147483647 ∧ 914321319<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q7_Dot1
end
