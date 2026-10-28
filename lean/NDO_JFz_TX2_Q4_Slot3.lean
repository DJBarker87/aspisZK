import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails14
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨37350156#u32,407139741#u32⟩,⟨419447709#u32,1635581430#u32⟩⟩,⟨⟨1270573021#u32,1724877082#u32⟩,⟨1915407542#u32,81408581#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 4 3 0 0 26%2147483647=37350156 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*633592471+855639275*1549551438+867568255*519054676+352063*954299161+1106523000*524737854+1554033304*759744483+1430280692*1898860494+1491718280*424604040+118514350*1539909554+1675652887*1449042899+1364884909*1617345534+1135303194*1242545416+304762092*538491220+1465393816*1315497880+824208172*657535988+1752653420*1213991842+1385409049*1267519951+1003904973*921142816+1298953245*237760809+2005758375*741966009+497936241*92034443+235809508*1723860806+1478307182*1176314644+1858903615*1095665473+628035096*1654912159+1244951250*40660285)%2147483647=37350156
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 4 3 1 0 26%2147483647=407139741 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*633592471+1483149559*1549551438+655227887*519054676+39062738*954299161+729079828*524737854+67370206*759744483+1685049618*1898860494+385547620*424604040+1786803209*1539909554+779721715*1449042899+594709522*1617345534+338788461*1242545416+526756808*538491220+184076238*1315497880+1852498770*657535988+2102463508*1213991842+1086671526*1267519951+1147694576*921142816+1504805752*237760809+2005073905*741966009+185008025*92034443+1485990146*1723860806+1255280192*1176314644+1018329259*1095665473+570157693*1654912159+1511904630*40660285)%2147483647=407139741
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 4 3 2 0 26%2147483647=419447709 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*633592471+1898717401*1549551438+1032732628*519054676+1313565596*954299161+1074182998*524737854+1410213748*759744483+1182702806*1898860494+321711020*424604040+2062791928*1539909554+1188803754*1449042899+2038502201*1617345534+735931834*1242545416+1330533011*538491220+1052874750*1315497880+950153811*657535988+1225424092*1213991842+1659116453*1267519951+1474177753*921142816+2073609211*237760809+1602919019*741966009+1865917845*92034443+1085624123*1723860806+1837870964*1176314644+1550509101*1095665473+1661725734*1654912159+2066655336*40660285)%2147483647=419447709
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 4 3 3 0 26%2147483647=1635581430 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*633592471+1849775942*1549551438+656039795*519054676+1840648083*954299161+246996287*524737854+1369248953*759744483+1132591724*1898860494+92744917*424604040+1719480363*1539909554+1266677922*1449042899+377386917*1617345534+735227219*1242545416+465096431*538491220+451889791*1315497880+1379836302*657535988+618598847*1213991842+1624084534*1267519951+1511477847*921142816+1840812326*237760809+185546252*741966009+2145463598*92034443+82870699*1723860806+1625323762*1176314644+1843639311*1095665473+1777269271*1654912159+1645120956*40660285)%2147483647=1635581430
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 4 3 4 0 26%2147483647=1270573021 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*633592471+1112406525*1549551438+1345999435*519054676+752376469*954299161+634588140*524737854+1419170319*759744483+1702860885*1898860494+710076517*424604040+1256487405*1539909554+1114745059*1449042899+1137838899*1617345534+1254184109*1242545416+1038210451*538491220+274378589*1315497880+171986381*657535988+1536678585*1213991842+1305878831*1267519951+1335902916*921142816+1755193245*237760809+2023391453*741966009+293456010*92034443+1751078325*1723860806+1423042536*1176314644+1749638204*1095665473+1345811362*1654912159+1284924881*40660285)%2147483647=1270573021
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 4 3 5 0 26%2147483647=1724877082 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*633592471+1796814865*1549551438+1253123171*519054676+1317611639*954299161+1559245386*524737854+1866942376*759744483+1973593402*1898860494+47019780*424604040+1353487525*1539909554+1840161555*1449042899+2003659556*1617345534+200559114*1242545416+334988447*538491220+2023650872*1315497880+1296497964*657535988+34285357*1213991842+1685894190*1267519951+995962325*921142816+1295624230*237760809+1199631211*741966009+1948677857*92034443+1425322328*1723860806+1466877680*1176314644+702011012*1095665473+937706871*1654912159+455802666*40660285)%2147483647=1724877082
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 4 3 6 0 26%2147483647=1915407542 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*633592471+1838939499*1549551438+1353876630*519054676+1258713036*954299161+1947503436*524737854+1271796599*759744483+1660157177*1898860494+564707688*424604040+1858113864*1539909554+1015817431*1449042899+1264608004*1617345534+735383960*1242545416+221696734*538491220+1297524163*1315497880+109088572*657535988+792206628*1213991842+1921581249*1267519951+94118806*921142816+476103426*237760809+239612482*741966009+177052717*92034443+826458039*1723860806+1923715623*1176314644+1014161165*1095665473+1341609618*1654912159+786325583*40660285)%2147483647=1915407542
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 4 3 7 0 26%2147483647=81408581 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*633592471+418714188*1549551438+1675147475*519054676+1674326661*954299161+547797802*524737854+2073962627*759744483+897270857*1898860494+1582958967*424604040+49892701*1539909554+1256824732*1449042899+1435903714*1617345534+742583315*1242545416+1789294768*538491220+13407412*1315497880+518661610*657535988+1259751297*1213991842+1695663205*1267519951+2068940067*921142816+940478841*237760809+1982757556*741966009+1956713516*92034443+863066484*1723860806+522298462*1176314644+1343575777*1095665473+771712139*1654912159+157728743*40660285)%2147483647=81408581
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 4 3
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
end AspisR1.JFz_TX2_Q4_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4906631396#u64 3118564022#u64 7040318955#u64 3962997010#u64⟩,⟨pack 3194394131#u64 1447963958#u64 6423614453#u64 4048444583#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 6802777924968946671#u64 2997327346818627592#u64 10762171792118049145#u64 5309985526153269675#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1353255284#u32 481405776#u32 1117794909#u32 1315848403#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1353255284#u32) (JFs_TX2_RawMath.extend 481405776#u32) (JFs_TX2_RawMath.extend 1117794909#u32) (JFs_TX2_RawMath.extend 1315848403#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1353255284#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1353255284#u32) (JFs_TX2_RawMath.extend 481405776#u32) (JFs_TX2_RawMath.extend 1117794909#u32) (JFs_TX2_RawMath.extend 1315848403#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 481405776#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1353255284#u32) (JFs_TX2_RawMath.extend 481405776#u32) (JFs_TX2_RawMath.extend 1117794909#u32) (JFs_TX2_RawMath.extend 1315848403#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1117794909#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1353255284#u32) (JFs_TX2_RawMath.extend 481405776#u32) (JFs_TX2_RawMath.extend 1117794909#u32) (JFs_TX2_RawMath.extend 1315848403#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1315848403#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4617802478102716493#u64 1899304347105676987#u64 9859411140654219154#u64 5791097690814292818#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1353255284#u32 481405776#u32 1117794909#u32 1315848403#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1353255284#u32) (JFs_TX2_RawMath.extend 481405776#u32) (JFs_TX2_RawMath.extend 1117794909#u32) (JFs_TX2_RawMath.extend 1315848403#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1353255284#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1353255284#u32) (JFs_TX2_RawMath.extend 481405776#u32) (JFs_TX2_RawMath.extend 1117794909#u32) (JFs_TX2_RawMath.extend 1315848403#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 481405776#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1353255284#u32) (JFs_TX2_RawMath.extend 481405776#u32) (JFs_TX2_RawMath.extend 1117794909#u32) (JFs_TX2_RawMath.extend 1315848403#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1117794909#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1353255284#u32) (JFs_TX2_RawMath.extend 481405776#u32) (JFs_TX2_RawMath.extend 1117794909#u32) (JFs_TX2_RawMath.extend 1315848403#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1315848403#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails14.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value0_3=
      ok (.Ok (pack 1353255284#u32 481405776#u32 1117794909#u32 1315848403#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1353255284<2147483647 ∧ 481405776<2147483647) ∧ (1117794909<2147483647 ∧ 1315848403<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1353255284#u32 481405776#u32 1117794909#u32 1315848403#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1353255284#u32 481405776#u32 1117794909#u32 1315848403#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q4_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4906631396#u64 3118564022#u64 7040318955#u64 3962997010#u64⟩,⟨pack 3194394131#u64 1447963958#u64 6423614453#u64 4048444583#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8658471304#u64 5714320052#u64 13721446251#u64 8802373987#u64⟩,⟨pack 6129383971#u64 3538872027#u64 11822363281#u64 7744751174#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 7594481393432166262#u64 3815524405418731912#u64 13055496421935744986#u64 9077942469139390249#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1880014731#u32 1640518442#u32 2000529660#u32 1793694926#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1880014731#u32) (JFs_TX2_RawMath.extend 1640518442#u32) (JFs_TX2_RawMath.extend 2000529660#u32) (JFs_TX2_RawMath.extend 1793694926#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1880014731#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1880014731#u32) (JFs_TX2_RawMath.extend 1640518442#u32) (JFs_TX2_RawMath.extend 2000529660#u32) (JFs_TX2_RawMath.extend 1793694926#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1640518442#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1880014731#u32) (JFs_TX2_RawMath.extend 1640518442#u32) (JFs_TX2_RawMath.extend 2000529660#u32) (JFs_TX2_RawMath.extend 1793694926#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2000529660#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1880014731#u32) (JFs_TX2_RawMath.extend 1640518442#u32) (JFs_TX2_RawMath.extend 2000529660#u32) (JFs_TX2_RawMath.extend 1793694926#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1793694926#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5430627114849498851#u64 1508423261267082168#u64 10011541900544841211#u64 3463420423661687955#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1880014731#u32 1640518442#u32 2000529660#u32 1793694926#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1880014731#u32) (JFs_TX2_RawMath.extend 1640518442#u32) (JFs_TX2_RawMath.extend 2000529660#u32) (JFs_TX2_RawMath.extend 1793694926#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1880014731#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1880014731#u32) (JFs_TX2_RawMath.extend 1640518442#u32) (JFs_TX2_RawMath.extend 2000529660#u32) (JFs_TX2_RawMath.extend 1793694926#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1640518442#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1880014731#u32) (JFs_TX2_RawMath.extend 1640518442#u32) (JFs_TX2_RawMath.extend 2000529660#u32) (JFs_TX2_RawMath.extend 1793694926#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2000529660#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1880014731#u32) (JFs_TX2_RawMath.extend 1640518442#u32) (JFs_TX2_RawMath.extend 2000529660#u32) (JFs_TX2_RawMath.extend 1793694926#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1793694926#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails14.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value1_3=
      ok (.Ok (pack 1880014731#u32 1640518442#u32 2000529660#u32 1793694926#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1880014731<2147483647 ∧ 1640518442<2147483647) ∧ (2000529660<2147483647 ∧ 1793694926<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1880014731#u32 1640518442#u32 2000529660#u32 1793694926#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4906631396#u64 3118564022#u64 7040318955#u64 3962997010#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1880014731#u32 1640518442#u32 2000529660#u32 1793694926#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3194394131#u64 1447963958#u64 6423614453#u64 4048444583#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q4_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8658471304#u64 5714320052#u64 13721446251#u64 8802373987#u64⟩,⟨pack 6129383971#u64 3538872027#u64 11822363281#u64 7744751174#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 12269564455#u64 7965301985#u64 20141460760#u64 10098717378#u64⟩,⟨pack 9770687160#u64 5647268699#u64 18009594685#u64 9250593458#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4722392980897024469#u64 428865616271899691#u64 9598470748448516377#u64 1066242996584613033#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 516792983#u32 271389441#u32 574787231#u32 254726861#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 516792983#u32) (JFs_TX2_RawMath.extend 271389441#u32) (JFs_TX2_RawMath.extend 574787231#u32) (JFs_TX2_RawMath.extend 254726861#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 516792983#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 516792983#u32) (JFs_TX2_RawMath.extend 271389441#u32) (JFs_TX2_RawMath.extend 574787231#u32) (JFs_TX2_RawMath.extend 254726861#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 271389441#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 516792983#u32) (JFs_TX2_RawMath.extend 271389441#u32) (JFs_TX2_RawMath.extend 574787231#u32) (JFs_TX2_RawMath.extend 254726861#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 574787231#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 516792983#u32) (JFs_TX2_RawMath.extend 271389441#u32) (JFs_TX2_RawMath.extend 574787231#u32) (JFs_TX2_RawMath.extend 254726861#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 254726861#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5027479456453721274#u64 1436733683700267304#u64 10375625555143714748#u64 3036960276897754588#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 516792983#u32 271389441#u32 574787231#u32 254726861#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 516792983#u32) (JFs_TX2_RawMath.extend 271389441#u32) (JFs_TX2_RawMath.extend 574787231#u32) (JFs_TX2_RawMath.extend 254726861#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 516792983#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 516792983#u32) (JFs_TX2_RawMath.extend 271389441#u32) (JFs_TX2_RawMath.extend 574787231#u32) (JFs_TX2_RawMath.extend 254726861#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 271389441#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 516792983#u32) (JFs_TX2_RawMath.extend 271389441#u32) (JFs_TX2_RawMath.extend 574787231#u32) (JFs_TX2_RawMath.extend 254726861#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 574787231#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 516792983#u32) (JFs_TX2_RawMath.extend 271389441#u32) (JFs_TX2_RawMath.extend 574787231#u32) (JFs_TX2_RawMath.extend 254726861#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 254726861#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails14.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value2_3=
      ok (.Ok (pack 516792983#u32 271389441#u32 574787231#u32 254726861#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (516792983<2147483647 ∧ 271389441<2147483647) ∧ (574787231<2147483647 ∧ 254726861<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 516792983#u32 271389441#u32 574787231#u32 254726861#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 8658471304#u64 5714320052#u64 13721446251#u64 8802373987#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 516792983#u32 271389441#u32 574787231#u32 254726861#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6129383971#u64 3538872027#u64 11822363281#u64 7744751174#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q4_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1532146220#u32,1522851044#u32⟩,⟨814107937#u32,1508782790#u32⟩⟩,⟨⟨1180752572#u32,1352301405#u32⟩,⟨829725509#u32,660658870#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q4_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q4_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=12269564455%2147483647 at h0
  norm_num at h0
  have e0 : a0=1532146220#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7965301985%2147483647 at h1
  norm_num at h1
  have e1 : a1=1522851044#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=20141460760%2147483647 at h2
  norm_num at h2
  have e2 : a2=814107937#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10098717378%2147483647 at h3
  norm_num at h3
  have e3 : a3=1508782790#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9770687160%2147483647 at h4
  norm_num at h4
  have e4 : a4=1180752572#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5647268699%2147483647 at h5
  norm_num at h5
  have e5 : a5=1352301405#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=18009594685%2147483647 at h6
  norm_num at h6
  have e6 : a6=829725509#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=9250593458%2147483647 at h7
  norm_num at h7
  have e7 : a7=660658870#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q4_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails14.value0_3
      from JFr_TX2_Tails14.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails14.value1_3
      from JFr_TX2_Tails14.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails14.value2_3
      from JFr_TX2_Tails14.source2_3,
    JFz_TX2_Q4_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q4_Raw30.after=JFz_TX2_Q4_Raw31.before := rfl
  have same2 : JFz_TX2_Q4_Raw31.after=JFz_TX2_Q4_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q4_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q4_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q4_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1569496376#u32,1929990785#u32⟩,⟨1233555646#u32,996880573#u32⟩⟩,⟨⟨303841946#u32,929694840#u32⟩,⟨597649404#u32,742067451#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1569496376<2147483647 ∧ 1929990785<2147483647) ∧ (1233555646<2147483647 ∧ 996880573<2147483647)) ∧
    ((303841946<2147483647 ∧ 929694840<2147483647) ∧ (597649404<2147483647 ∧ 742067451<2147483647))
  omega
theorem addition : decode JFz_TX2_Q4_Head3.value+decode JFz_TX2_Q4_Tail3.value=decode value := by
  change (⟨⟨⟨37350156,407139741⟩,⟨419447709,1635581430⟩⟩,⟨⟨1270573021,1724877082⟩,⟨1915407542,81408581⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1532146220,1522851044⟩,⟨814107937,1508782790⟩⟩,⟨⟨1180752572,1352301405⟩,⟨829725509,660658870⟩⟩⟩=⟨⟨⟨1569496376,1929990785⟩,⟨1233555646,996880573⟩⟩,⟨⟨303841946,929694840⟩,⟨597649404,742067451⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 4 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q4_Head3.value JFz_TX2_Q4_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q4_Head3.source,
      JFz_TX2_Q4_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q4_Head3.value := by
    change ((37350156<2147483647 ∧ 407139741<2147483647) ∧ (419447709<2147483647 ∧ 1635581430<2147483647)) ∧
      ((1270573021<2147483647 ∧ 1724877082<2147483647) ∧ (1915407542<2147483647 ∧ 81408581<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q4_Tail3.value := by
    change ((1532146220<2147483647 ∧ 1522851044<2147483647) ∧ (814107937<2147483647 ∧ 1508782790<2147483647)) ∧
      ((1180752572<2147483647 ∧ 1352301405<2147483647) ∧ (829725509<2147483647 ∧ 660658870<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q4_Dot3
end
