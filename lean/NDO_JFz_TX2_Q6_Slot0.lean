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
namespace AspisR1.JFz_TX2_Q6_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨601940147#u32,1160369491#u32⟩,⟨461961897#u32,817927786#u32⟩⟩,⟨⟨1231990807#u32,667277129#u32⟩,⟨239733352#u32,1852183609#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 6 0 0 0 26%2147483647=601940147 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1154790530+855639275*414489403+867568255*2115918169+352063*658436828+1106523000*73803498+1554033304*791139881+1430280692*801403690+1491718280*2021829543+118514350*662238949+1675652887*1755274902+1364884909*1420204690+1135303194*2134411043+304762092*1875948838+1465393816*2052783151+824208172*40649997+1752653420*1184925504+1385409049*1244985959+1003904973*438397484+1298953245*1954386336+2005758375*349821277+497936241*177122515+235809508*1139981419+1478307182*1447326145+1858903615*1880640988+628035096*587609521+1244951250*1304578296)%2147483647=601940147
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 6 0 1 0 26%2147483647=1160369491 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1154790530+1483149559*414489403+655227887*2115918169+39062738*658436828+729079828*73803498+67370206*791139881+1685049618*801403690+385547620*2021829543+1786803209*662238949+779721715*1755274902+594709522*1420204690+338788461*2134411043+526756808*1875948838+184076238*2052783151+1852498770*40649997+2102463508*1184925504+1086671526*1244985959+1147694576*438397484+1504805752*1954386336+2005073905*349821277+185008025*177122515+1485990146*1139981419+1255280192*1447326145+1018329259*1880640988+570157693*587609521+1511904630*1304578296)%2147483647=1160369491
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 6 0 2 0 26%2147483647=461961897 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1154790530+1898717401*414489403+1032732628*2115918169+1313565596*658436828+1074182998*73803498+1410213748*791139881+1182702806*801403690+321711020*2021829543+2062791928*662238949+1188803754*1755274902+2038502201*1420204690+735931834*2134411043+1330533011*1875948838+1052874750*2052783151+950153811*40649997+1225424092*1184925504+1659116453*1244985959+1474177753*438397484+2073609211*1954386336+1602919019*349821277+1865917845*177122515+1085624123*1139981419+1837870964*1447326145+1550509101*1880640988+1661725734*587609521+2066655336*1304578296)%2147483647=461961897
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 6 0 3 0 26%2147483647=817927786 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1154790530+1849775942*414489403+656039795*2115918169+1840648083*658436828+246996287*73803498+1369248953*791139881+1132591724*801403690+92744917*2021829543+1719480363*662238949+1266677922*1755274902+377386917*1420204690+735227219*2134411043+465096431*1875948838+451889791*2052783151+1379836302*40649997+618598847*1184925504+1624084534*1244985959+1511477847*438397484+1840812326*1954386336+185546252*349821277+2145463598*177122515+82870699*1139981419+1625323762*1447326145+1843639311*1880640988+1777269271*587609521+1645120956*1304578296)%2147483647=817927786
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 6 0 4 0 26%2147483647=1231990807 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1154790530+1112406525*414489403+1345999435*2115918169+752376469*658436828+634588140*73803498+1419170319*791139881+1702860885*801403690+710076517*2021829543+1256487405*662238949+1114745059*1755274902+1137838899*1420204690+1254184109*2134411043+1038210451*1875948838+274378589*2052783151+171986381*40649997+1536678585*1184925504+1305878831*1244985959+1335902916*438397484+1755193245*1954386336+2023391453*349821277+293456010*177122515+1751078325*1139981419+1423042536*1447326145+1749638204*1880640988+1345811362*587609521+1284924881*1304578296)%2147483647=1231990807
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 6 0 5 0 26%2147483647=667277129 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1154790530+1796814865*414489403+1253123171*2115918169+1317611639*658436828+1559245386*73803498+1866942376*791139881+1973593402*801403690+47019780*2021829543+1353487525*662238949+1840161555*1755274902+2003659556*1420204690+200559114*2134411043+334988447*1875948838+2023650872*2052783151+1296497964*40649997+34285357*1184925504+1685894190*1244985959+995962325*438397484+1295624230*1954386336+1199631211*349821277+1948677857*177122515+1425322328*1139981419+1466877680*1447326145+702011012*1880640988+937706871*587609521+455802666*1304578296)%2147483647=667277129
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 6 0 6 0 26%2147483647=239733352 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1154790530+1838939499*414489403+1353876630*2115918169+1258713036*658436828+1947503436*73803498+1271796599*791139881+1660157177*801403690+564707688*2021829543+1858113864*662238949+1015817431*1755274902+1264608004*1420204690+735383960*2134411043+221696734*1875948838+1297524163*2052783151+109088572*40649997+792206628*1184925504+1921581249*1244985959+94118806*438397484+476103426*1954386336+239612482*349821277+177052717*177122515+826458039*1139981419+1923715623*1447326145+1014161165*1880640988+1341609618*587609521+786325583*1304578296)%2147483647=239733352
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 6 0 7 0 26%2147483647=1852183609 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1154790530+418714188*414489403+1675147475*2115918169+1674326661*658436828+547797802*73803498+2073962627*791139881+897270857*801403690+1582958967*2021829543+49892701*662238949+1256824732*1755274902+1435903714*1420204690+742583315*2134411043+1789294768*1875948838+13407412*2052783151+518661610*40649997+1259751297*1184925504+1695663205*1244985959+2068940067*438397484+940478841*1954386336+1982757556*349821277+1956713516*177122515+863066484*1139981419+522298462*1447326145+1343575777*1880640988+771712139*587609521+157728743*1304578296)%2147483647=1852183609
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 6 0
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
end AspisR1.JFz_TX2_Q6_Head0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw00
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3938190584#u64 3281779339#u64 4987147534#u64 2736102735#u64⟩,⟨pack 2948214170#u64 2171262293#u64 4373360488#u64 4268334483#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4380615828465639219#u64 5685711933673345225#u64 9107531974296792295#u64 4438735575941546069#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1164046758#u32 1868452897#u32 338085521#u32 882109740#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1164046758#u32) (JFs_TX2_RawMath.extend 1868452897#u32) (JFs_TX2_RawMath.extend 338085521#u32) (JFs_TX2_RawMath.extend 882109740#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1164046758#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1164046758#u32) (JFs_TX2_RawMath.extend 1868452897#u32) (JFs_TX2_RawMath.extend 338085521#u32) (JFs_TX2_RawMath.extend 882109740#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1868452897#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1164046758#u32) (JFs_TX2_RawMath.extend 1868452897#u32) (JFs_TX2_RawMath.extend 338085521#u32) (JFs_TX2_RawMath.extend 882109740#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 338085521#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1164046758#u32) (JFs_TX2_RawMath.extend 1868452897#u32) (JFs_TX2_RawMath.extend 338085521#u32) (JFs_TX2_RawMath.extend 882109740#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 882109740#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2807119922555020342#u64 2284148417544649617#u64 6768166219679889606#u64 7079459895651272459#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1164046758#u32 1868452897#u32 338085521#u32 882109740#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1164046758#u32) (JFs_TX2_RawMath.extend 1868452897#u32) (JFs_TX2_RawMath.extend 338085521#u32) (JFs_TX2_RawMath.extend 882109740#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1164046758#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1164046758#u32) (JFs_TX2_RawMath.extend 1868452897#u32) (JFs_TX2_RawMath.extend 338085521#u32) (JFs_TX2_RawMath.extend 882109740#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1868452897#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1164046758#u32) (JFs_TX2_RawMath.extend 1868452897#u32) (JFs_TX2_RawMath.extend 338085521#u32) (JFs_TX2_RawMath.extend 882109740#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 338085521#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1164046758#u32) (JFs_TX2_RawMath.extend 1868452897#u32) (JFs_TX2_RawMath.extend 338085521#u32) (JFs_TX2_RawMath.extend 882109740#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 882109740#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails16.value0_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value0_0=
      ok (.Ok (pack 1164046758#u32 1868452897#u32 338085521#u32 882109740#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1164046758<2147483647 ∧ 1868452897<2147483647) ∧ (338085521<2147483647 ∧ 882109740<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1164046758#u32 1868452897#u32 338085521#u32 882109740#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1164046758#u32 1868452897#u32 338085521#u32 882109740#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q6_Raw00
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3938190584#u64 3281779339#u64 4987147534#u64 2736102735#u64⟩,⟨pack 2948214170#u64 2171262293#u64 4373360488#u64 4268334483#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8118846900#u64 4714736531#u64 9850616231#u64 5014399037#u64⟩,⟨pack 5273860001#u64 2517174750#u64 10149611272#u64 5802652344#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5731420134008655935#u64 1543630391713270197#u64 9859621287548801524#u64 2825130562289813600#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 716570780#u32 672154398#u32 307909038#u32 400967314#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716570780#u32) (JFs_TX2_RawMath.extend 672154398#u32) (JFs_TX2_RawMath.extend 307909038#u32) (JFs_TX2_RawMath.extend 400967314#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 716570780#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716570780#u32) (JFs_TX2_RawMath.extend 672154398#u32) (JFs_TX2_RawMath.extend 307909038#u32) (JFs_TX2_RawMath.extend 400967314#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 672154398#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716570780#u32) (JFs_TX2_RawMath.extend 672154398#u32) (JFs_TX2_RawMath.extend 307909038#u32) (JFs_TX2_RawMath.extend 400967314#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 307909038#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716570780#u32) (JFs_TX2_RawMath.extend 672154398#u32) (JFs_TX2_RawMath.extend 307909038#u32) (JFs_TX2_RawMath.extend 400967314#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 400967314#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4912592112270473480#u64 605157443211775375#u64 9271689514155460262#u64 1050389978335173864#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 716570780#u32 672154398#u32 307909038#u32 400967314#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716570780#u32) (JFs_TX2_RawMath.extend 672154398#u32) (JFs_TX2_RawMath.extend 307909038#u32) (JFs_TX2_RawMath.extend 400967314#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 716570780#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716570780#u32) (JFs_TX2_RawMath.extend 672154398#u32) (JFs_TX2_RawMath.extend 307909038#u32) (JFs_TX2_RawMath.extend 400967314#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 672154398#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716570780#u32) (JFs_TX2_RawMath.extend 672154398#u32) (JFs_TX2_RawMath.extend 307909038#u32) (JFs_TX2_RawMath.extend 400967314#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 307909038#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 716570780#u32) (JFs_TX2_RawMath.extend 672154398#u32) (JFs_TX2_RawMath.extend 307909038#u32) (JFs_TX2_RawMath.extend 400967314#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 400967314#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails16.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value1_0=
      ok (.Ok (pack 716570780#u32 672154398#u32 307909038#u32 400967314#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (716570780<2147483647 ∧ 672154398<2147483647) ∧ (307909038<2147483647 ∧ 400967314<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 716570780#u32 672154398#u32 307909038#u32 400967314#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3938190584#u64 3281779339#u64 4987147534#u64 2736102735#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 716570780#u32 672154398#u32 307909038#u32 400967314#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2948214170#u64 2171262293#u64 4373360488#u64 4268334483#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q6_Raw01
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8118846900#u64 4714736531#u64 9850616231#u64 5014399037#u64⟩,⟨pack 5273860001#u64 2517174750#u64 10149611272#u64 5802652344#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 11964958663#u64 6910246817#u64 15155024975#u64 8112448993#u64⟩,⟨pack 8206695420#u64 5625111453#u64 15489422581#u64 10233416609#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 3922722297791538121#u64 1088280388769948048#u64 8568912272441020937#u64 2650375016148398483#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 453141450#u32 1635862880#u32 1103860147#u32 649798514#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 453141450#u32) (JFs_TX2_RawMath.extend 1635862880#u32) (JFs_TX2_RawMath.extend 1103860147#u32) (JFs_TX2_RawMath.extend 649798514#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 453141450#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 453141450#u32) (JFs_TX2_RawMath.extend 1635862880#u32) (JFs_TX2_RawMath.extend 1103860147#u32) (JFs_TX2_RawMath.extend 649798514#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1635862880#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 453141450#u32) (JFs_TX2_RawMath.extend 1635862880#u32) (JFs_TX2_RawMath.extend 1103860147#u32) (JFs_TX2_RawMath.extend 649798514#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1103860147#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 453141450#u32) (JFs_TX2_RawMath.extend 1635862880#u32) (JFs_TX2_RawMath.extend 1103860147#u32) (JFs_TX2_RawMath.extend 649798514#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 649798514#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2392998458792623493#u64 3741058933002438449#u64 7953164423811066910#u64 7501657025502355014#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 453141450#u32 1635862880#u32 1103860147#u32 649798514#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 453141450#u32) (JFs_TX2_RawMath.extend 1635862880#u32) (JFs_TX2_RawMath.extend 1103860147#u32) (JFs_TX2_RawMath.extend 649798514#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 453141450#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 453141450#u32) (JFs_TX2_RawMath.extend 1635862880#u32) (JFs_TX2_RawMath.extend 1103860147#u32) (JFs_TX2_RawMath.extend 649798514#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1635862880#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 453141450#u32) (JFs_TX2_RawMath.extend 1635862880#u32) (JFs_TX2_RawMath.extend 1103860147#u32) (JFs_TX2_RawMath.extend 649798514#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1103860147#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 453141450#u32) (JFs_TX2_RawMath.extend 1635862880#u32) (JFs_TX2_RawMath.extend 1103860147#u32) (JFs_TX2_RawMath.extend 649798514#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 649798514#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails16.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails16.value2_0=
      ok (.Ok (pack 453141450#u32 1635862880#u32 1103860147#u32 649798514#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (453141450<2147483647 ∧ 1635862880<2147483647) ∧ (1103860147<2147483647 ∧ 649798514<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 453141450#u32 1635862880#u32 1103860147#u32 649798514#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 8118846900#u64 4714736531#u64 9850616231#u64 5014399037#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 453141450#u32 1635862880#u32 1103860147#u32 649798514#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5273860001#u64 2517174750#u64 10149611272#u64 5802652344#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q6_Raw02
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Tail0
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1227540428#u32,467795876#u32⟩,⟨122639446#u32,1669998052#u32⟩⟩,⟨⟨1764244479#u32,1330144159#u32⟩,⟨457037052#u32,1643482021#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q6_Raw02.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q6_Raw02.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=11964958663%2147483647 at h0
  norm_num at h0
  have e0 : a0=1227540428#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6910246817%2147483647 at h1
  norm_num at h1
  have e1 : a1=467795876#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15155024975%2147483647 at h2
  norm_num at h2
  have e2 : a2=122639446#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=8112448993%2147483647 at h3
  norm_num at h3
  have e3 : a3=1669998052#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8206695420%2147483647 at h4
  norm_num at h4
  have e4 : a4=1764244479#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5625111453%2147483647 at h5
  norm_num at h5
  have e5 : a5=1330144159#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15489422581%2147483647 at h6
  norm_num at h6
  have e6 : a6=457037052#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10233416609%2147483647 at h7
  norm_num at h7
  have e7 : a7=1643482021#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q6_Raw00.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JFr_TX2_Tails16.value0_0
      from JFr_TX2_Tails16.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JFr_TX2_Tails16.value1_0
      from JFr_TX2_Tails16.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 6))
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JFr_TX2_Tails16.value2_0
      from JFr_TX2_Tails16.source2_0,
    JFz_TX2_Q6_Raw00.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q6_Raw00.after=JFz_TX2_Q6_Raw01.before := rfl
  have same2 : JFz_TX2_Q6_Raw01.after=JFz_TX2_Q6_Raw02.before := rfl
  simp only [same1,JFz_TX2_Q6_Raw01.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q6_Raw02.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q6_Tail0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q6_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1829480575#u32,1628165367#u32⟩,⟨584601343#u32,340442191#u32⟩⟩,⟨⟨848751639#u32,1997421288#u32⟩,⟨696770404#u32,1348181983#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1829480575<2147483647 ∧ 1628165367<2147483647) ∧ (584601343<2147483647 ∧ 340442191<2147483647)) ∧
    ((848751639<2147483647 ∧ 1997421288<2147483647) ∧ (696770404<2147483647 ∧ 1348181983<2147483647))
  omega
theorem addition : decode JFz_TX2_Q6_Head0.value+decode JFz_TX2_Q6_Tail0.value=decode value := by
  change (⟨⟨⟨601940147,1160369491⟩,⟨461961897,817927786⟩⟩,⟨⟨1231990807,667277129⟩,⟨239733352,1852183609⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1227540428,467795876⟩,⟨122639446,1669998052⟩⟩,⟨⟨1764244479,1330144159⟩,⟨457037052,1643482021⟩⟩⟩=⟨⟨⟨1829480575,1628165367⟩,⟨584601343,340442191⟩⟩,⟨⟨848751639,1997421288⟩,⟨696770404,1348181983⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 6)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 6 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q6_Head0.value JFz_TX2_Q6_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q6_Head0.source,
      JFz_TX2_Q6_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q6_Head0.value := by
    change ((601940147<2147483647 ∧ 1160369491<2147483647) ∧ (461961897<2147483647 ∧ 817927786<2147483647)) ∧
      ((1231990807<2147483647 ∧ 667277129<2147483647) ∧ (239733352<2147483647 ∧ 1852183609<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q6_Tail0.value := by
    change ((1227540428<2147483647 ∧ 467795876<2147483647) ∧ (122639446<2147483647 ∧ 1669998052<2147483647)) ∧
      ((1764244479<2147483647 ∧ 1330144159<2147483647) ∧ (457037052<2147483647 ∧ 1643482021<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q6_Dot0
end
