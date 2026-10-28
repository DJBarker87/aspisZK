import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails18
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨325470336#u32,1629824597#u32⟩,⟨1027046303#u32,1214659801#u32⟩⟩,⟨⟨80717226#u32,350563441#u32⟩,⟨332114538#u32,213721355#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 8 3 0 0 26%2147483647=325470336 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*60879567+855639275*17471509+867568255*1081625464+352063*1710150987+1106523000*1281649084+1554033304*1591176997+1430280692*235904891+1491718280*847501171+118514350*471624392+1675652887*1646383855+1364884909*546883094+1135303194*648849306+304762092*1789211694+1465393816*403885958+824208172*368671809+1752653420*1370209148+1385409049*246604779+1003904973*1916172790+1298953245*1337129091+2005758375*757799431+497936241*257553107+235809508*2117821763+1478307182*2065804289+1858903615*1580847273+628035096*2028295753+1244951250*193852602)%2147483647=325470336
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 8 3 1 0 26%2147483647=1629824597 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*60879567+1483149559*17471509+655227887*1081625464+39062738*1710150987+729079828*1281649084+67370206*1591176997+1685049618*235904891+385547620*847501171+1786803209*471624392+779721715*1646383855+594709522*546883094+338788461*648849306+526756808*1789211694+184076238*403885958+1852498770*368671809+2102463508*1370209148+1086671526*246604779+1147694576*1916172790+1504805752*1337129091+2005073905*757799431+185008025*257553107+1485990146*2117821763+1255280192*2065804289+1018329259*1580847273+570157693*2028295753+1511904630*193852602)%2147483647=1629824597
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 8 3 2 0 26%2147483647=1027046303 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*60879567+1898717401*17471509+1032732628*1081625464+1313565596*1710150987+1074182998*1281649084+1410213748*1591176997+1182702806*235904891+321711020*847501171+2062791928*471624392+1188803754*1646383855+2038502201*546883094+735931834*648849306+1330533011*1789211694+1052874750*403885958+950153811*368671809+1225424092*1370209148+1659116453*246604779+1474177753*1916172790+2073609211*1337129091+1602919019*757799431+1865917845*257553107+1085624123*2117821763+1837870964*2065804289+1550509101*1580847273+1661725734*2028295753+2066655336*193852602)%2147483647=1027046303
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 8 3 3 0 26%2147483647=1214659801 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*60879567+1849775942*17471509+656039795*1081625464+1840648083*1710150987+246996287*1281649084+1369248953*1591176997+1132591724*235904891+92744917*847501171+1719480363*471624392+1266677922*1646383855+377386917*546883094+735227219*648849306+465096431*1789211694+451889791*403885958+1379836302*368671809+618598847*1370209148+1624084534*246604779+1511477847*1916172790+1840812326*1337129091+185546252*757799431+2145463598*257553107+82870699*2117821763+1625323762*2065804289+1843639311*1580847273+1777269271*2028295753+1645120956*193852602)%2147483647=1214659801
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 8 3 4 0 26%2147483647=80717226 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*60879567+1112406525*17471509+1345999435*1081625464+752376469*1710150987+634588140*1281649084+1419170319*1591176997+1702860885*235904891+710076517*847501171+1256487405*471624392+1114745059*1646383855+1137838899*546883094+1254184109*648849306+1038210451*1789211694+274378589*403885958+171986381*368671809+1536678585*1370209148+1305878831*246604779+1335902916*1916172790+1755193245*1337129091+2023391453*757799431+293456010*257553107+1751078325*2117821763+1423042536*2065804289+1749638204*1580847273+1345811362*2028295753+1284924881*193852602)%2147483647=80717226
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 8 3 5 0 26%2147483647=350563441 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*60879567+1796814865*17471509+1253123171*1081625464+1317611639*1710150987+1559245386*1281649084+1866942376*1591176997+1973593402*235904891+47019780*847501171+1353487525*471624392+1840161555*1646383855+2003659556*546883094+200559114*648849306+334988447*1789211694+2023650872*403885958+1296497964*368671809+34285357*1370209148+1685894190*246604779+995962325*1916172790+1295624230*1337129091+1199631211*757799431+1948677857*257553107+1425322328*2117821763+1466877680*2065804289+702011012*1580847273+937706871*2028295753+455802666*193852602)%2147483647=350563441
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 8 3 6 0 26%2147483647=332114538 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*60879567+1838939499*17471509+1353876630*1081625464+1258713036*1710150987+1947503436*1281649084+1271796599*1591176997+1660157177*235904891+564707688*847501171+1858113864*471624392+1015817431*1646383855+1264608004*546883094+735383960*648849306+221696734*1789211694+1297524163*403885958+109088572*368671809+792206628*1370209148+1921581249*246604779+94118806*1916172790+476103426*1337129091+239612482*757799431+177052717*257553107+826458039*2117821763+1923715623*2065804289+1014161165*1580847273+1341609618*2028295753+786325583*193852602)%2147483647=332114538
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 8 3 7 0 26%2147483647=213721355 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*60879567+418714188*17471509+1675147475*1081625464+1674326661*1710150987+547797802*1281649084+2073962627*1591176997+897270857*235904891+1582958967*847501171+49892701*471624392+1256824732*1646383855+1435903714*546883094+742583315*648849306+1789294768*1789211694+13407412*403885958+518661610*368671809+1259751297*1370209148+1695663205*246604779+2068940067*1916172790+940478841*1337129091+1982757556*757799431+1956713516*257553107+863066484*2117821763+522298462*2065804289+1343575777*1580847273+771712139*2028295753+157728743*193852602)%2147483647=213721355
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 8 3
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
end AspisR1.JFz_TX2_Q8_Head3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw30
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3416266271#u64 3640395569#u64 6561463049#u64 2707821067#u64⟩,⟨pack 3289655365#u64 961088041#u64 5719307018#u64 4792043004#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4557770292379725378#u64 4406072333395099727#u64 12572293445686949499#u64 5481015716012694665#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 942083152#u32 1420686064#u32 1794207387#u32 601123917#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 942083152#u32) (JFs_TX2_RawMath.extend 1420686064#u32) (JFs_TX2_RawMath.extend 1794207387#u32) (JFs_TX2_RawMath.extend 601123917#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 942083152#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 942083152#u32) (JFs_TX2_RawMath.extend 1420686064#u32) (JFs_TX2_RawMath.extend 1794207387#u32) (JFs_TX2_RawMath.extend 601123917#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1420686064#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 942083152#u32) (JFs_TX2_RawMath.extend 1420686064#u32) (JFs_TX2_RawMath.extend 1794207387#u32) (JFs_TX2_RawMath.extend 601123917#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1794207387#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 942083152#u32) (JFs_TX2_RawMath.extend 1420686064#u32) (JFs_TX2_RawMath.extend 1794207387#u32) (JFs_TX2_RawMath.extend 601123917#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 601123917#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3265065302323656982#u64 1807687886021895437#u64 8247571807137901906#u64 7383536936275777162#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 942083152#u32 1420686064#u32 1794207387#u32 601123917#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 942083152#u32) (JFs_TX2_RawMath.extend 1420686064#u32) (JFs_TX2_RawMath.extend 1794207387#u32) (JFs_TX2_RawMath.extend 601123917#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 942083152#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 942083152#u32) (JFs_TX2_RawMath.extend 1420686064#u32) (JFs_TX2_RawMath.extend 1794207387#u32) (JFs_TX2_RawMath.extend 601123917#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1420686064#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 942083152#u32) (JFs_TX2_RawMath.extend 1420686064#u32) (JFs_TX2_RawMath.extend 1794207387#u32) (JFs_TX2_RawMath.extend 601123917#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1794207387#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 942083152#u32) (JFs_TX2_RawMath.extend 1420686064#u32) (JFs_TX2_RawMath.extend 1794207387#u32) (JFs_TX2_RawMath.extend 601123917#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 601123917#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails18.value0_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value0_3=
      ok (.Ok (pack 942083152#u32 1420686064#u32 1794207387#u32 601123917#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (942083152<2147483647 ∧ 1420686064<2147483647) ∧ (1794207387<2147483647 ∧ 601123917<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 942083152#u32 1420686064#u32 1794207387#u32 601123917#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 942083152#u32 1420686064#u32 1794207387#u32 601123917#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q8_Raw30
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw31
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 3416266271#u64 3640395569#u64 6561463049#u64 2707821067#u64⟩,⟨pack 3289655365#u64 961088041#u64 5719307018#u64 4792043004#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6210756935#u64 5733689271#u64 12155299436#u64 8075108979#u64⟩,⟨pack 7192923827#u64 2105522558#u64 11550747853#u64 6971724997#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5909559276292708724#u64 4471769888891292283#u64 7669790303142414362#u64 7907820555740241565#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1091321985#u32 2136322414#u32 117829117#u32 1692655609#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1091321985#u32) (JFs_TX2_RawMath.extend 2136322414#u32) (JFs_TX2_RawMath.extend 117829117#u32) (JFs_TX2_RawMath.extend 1692655609#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1091321985#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1091321985#u32) (JFs_TX2_RawMath.extend 2136322414#u32) (JFs_TX2_RawMath.extend 117829117#u32) (JFs_TX2_RawMath.extend 1692655609#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2136322414#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1091321985#u32) (JFs_TX2_RawMath.extend 2136322414#u32) (JFs_TX2_RawMath.extend 117829117#u32) (JFs_TX2_RawMath.extend 1692655609#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 117829117#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1091321985#u32) (JFs_TX2_RawMath.extend 2136322414#u32) (JFs_TX2_RawMath.extend 117829117#u32) (JFs_TX2_RawMath.extend 1692655609#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1692655609#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4803248353986348179#u64 1639048931016477362#u64 8176200795979862824#u64 2724843846822928564#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1091321985#u32 2136322414#u32 117829117#u32 1692655609#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1091321985#u32) (JFs_TX2_RawMath.extend 2136322414#u32) (JFs_TX2_RawMath.extend 117829117#u32) (JFs_TX2_RawMath.extend 1692655609#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1091321985#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1091321985#u32) (JFs_TX2_RawMath.extend 2136322414#u32) (JFs_TX2_RawMath.extend 117829117#u32) (JFs_TX2_RawMath.extend 1692655609#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2136322414#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1091321985#u32) (JFs_TX2_RawMath.extend 2136322414#u32) (JFs_TX2_RawMath.extend 117829117#u32) (JFs_TX2_RawMath.extend 1692655609#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 117829117#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1091321985#u32) (JFs_TX2_RawMath.extend 2136322414#u32) (JFs_TX2_RawMath.extend 117829117#u32) (JFs_TX2_RawMath.extend 1692655609#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1692655609#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails18.value1_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value1_3=
      ok (.Ok (pack 1091321985#u32 2136322414#u32 117829117#u32 1692655609#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1091321985<2147483647 ∧ 2136322414<2147483647) ∧ (117829117<2147483647 ∧ 1692655609<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1091321985#u32 2136322414#u32 117829117#u32 1692655609#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3416266271#u64 3640395569#u64 6561463049#u64 2707821067#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1091321985#u32 2136322414#u32 117829117#u32 1692655609#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3289655365#u64 961088041#u64 5719307018#u64 4792043004#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q8_Raw31
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw32
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6210756935#u64 5733689271#u64 12155299436#u64 8075108979#u64⟩,⟨pack 7192923827#u64 2105522558#u64 11550747853#u64 6971724997#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 10103354436#u64 7233894609#u64 16960401028#u64 12015058445#u64⟩,⟨pack 9114996519#u64 5771308290#u64 16418469137#u64 14426082108#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4181202105424877739#u64 1887443309644233145#u64 8455389362874015857#u64 4284297656436332433#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1462329720#u32 2090616024#u32 1050967487#u32 1687202394#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1462329720#u32) (JFs_TX2_RawMath.extend 2090616024#u32) (JFs_TX2_RawMath.extend 1050967487#u32) (JFs_TX2_RawMath.extend 1687202394#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1462329720#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1462329720#u32) (JFs_TX2_RawMath.extend 2090616024#u32) (JFs_TX2_RawMath.extend 1050967487#u32) (JFs_TX2_RawMath.extend 1687202394#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2090616024#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1462329720#u32) (JFs_TX2_RawMath.extend 2090616024#u32) (JFs_TX2_RawMath.extend 1050967487#u32) (JFs_TX2_RawMath.extend 1687202394#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1050967487#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1462329720#u32) (JFs_TX2_RawMath.extend 2090616024#u32) (JFs_TX2_RawMath.extend 1050967487#u32) (JFs_TX2_RawMath.extend 1687202394#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1687202394#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3343947692479894281#u64 6413193831470004197#u64 7256787112861169000#u64 12058717297118683004#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1462329720#u32 2090616024#u32 1050967487#u32 1687202394#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1462329720#u32) (JFs_TX2_RawMath.extend 2090616024#u32) (JFs_TX2_RawMath.extend 1050967487#u32) (JFs_TX2_RawMath.extend 1687202394#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1462329720#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1462329720#u32) (JFs_TX2_RawMath.extend 2090616024#u32) (JFs_TX2_RawMath.extend 1050967487#u32) (JFs_TX2_RawMath.extend 1687202394#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2090616024#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1462329720#u32) (JFs_TX2_RawMath.extend 2090616024#u32) (JFs_TX2_RawMath.extend 1050967487#u32) (JFs_TX2_RawMath.extend 1687202394#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1050967487#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1462329720#u32) (JFs_TX2_RawMath.extend 2090616024#u32) (JFs_TX2_RawMath.extend 1050967487#u32) (JFs_TX2_RawMath.extend 1687202394#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1687202394#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails18.value2_3=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value2_3=
      ok (.Ok (pack 1462329720#u32 2090616024#u32 1050967487#u32 1687202394#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1462329720<2147483647 ∧ 2090616024<2147483647) ∧ (1050967487<2147483647 ∧ 1687202394<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1462329720#u32 2090616024#u32 1050967487#u32 1687202394#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6210756935#u64 5733689271#u64 12155299436#u64 8075108979#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1462329720#u32 2090616024#u32 1050967487#u32 1687202394#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7192923827#u64 2105522558#u64 11550747853#u64 6971724997#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q8_Raw32
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Tail3
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨1513419848#u32,791443668#u32⟩,⟨1928015499#u32,1277640210#u32⟩⟩,⟨⟨525061931#u32,1476340996#u32⟩,⟨1386083608#u32,1541180226#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q8_Raw32.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q8_Raw32.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=10103354436%2147483647 at h0
  norm_num at h0
  have e0 : a0=1513419848#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7233894609%2147483647 at h1
  norm_num at h1
  have e1 : a1=791443668#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=16960401028%2147483647 at h2
  norm_num at h2
  have e2 : a2=1928015499#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=12015058445%2147483647 at h3
  norm_num at h3
  have e3 : a3=1277640210#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9114996519%2147483647 at h4
  norm_num at h4
  have e4 : a4=525061931#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5771308290%2147483647 at h5
  norm_num at h5
  have e5 : a5=1476340996#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=16418469137%2147483647 at h6
  norm_num at h6
  have e6 : a6=1386083608#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=14426082108%2147483647 at h7
  norm_num at h7
  have e7 : a7=1541180226#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (3:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q8_Raw30.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 3 0) (JFr_TX2_Tails.stop 3 0)=ok JFr_TX2_Tails18.value0_3
      from JFr_TX2_Tails18.source0_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 3 1) (JFr_TX2_Tails.stop 3 1)=ok JFr_TX2_Tails18.value1_3
      from JFr_TX2_Tails18.source1_3,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 3 2) (JFr_TX2_Tails.stop 3 2)=ok JFr_TX2_Tails18.value2_3
      from JFr_TX2_Tails18.source2_3,
    JFz_TX2_Q8_Raw30.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q8_Raw30.after=JFz_TX2_Q8_Raw31.before := rfl
  have same2 : JFz_TX2_Q8_Raw31.after=JFz_TX2_Q8_Raw32.before := rfl
  simp only [same1,JFz_TX2_Q8_Raw31.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q8_Raw32.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q8_Tail3
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1838890184#u32,273784618#u32⟩,⟨807578155#u32,344816364#u32⟩⟩,⟨⟨605779157#u32,1826904437#u32⟩,⟨1718198146#u32,1754901581#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1838890184<2147483647 ∧ 273784618<2147483647) ∧ (807578155<2147483647 ∧ 344816364<2147483647)) ∧
    ((605779157<2147483647 ∧ 1826904437<2147483647) ∧ (1718198146<2147483647 ∧ 1754901581<2147483647))
  omega
theorem addition : decode JFz_TX2_Q8_Head3.value+decode JFz_TX2_Q8_Tail3.value=decode value := by
  change (⟨⟨⟨325470336,1629824597⟩,⟨1027046303,1214659801⟩⟩,⟨⟨80717226,350563441⟩,⟨332114538,213721355⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1513419848,791443668⟩,⟨1928015499,1277640210⟩⟩,⟨⟨525061931,1476340996⟩,⟨1386083608,1541180226⟩⟩⟩=⟨⟨⟨1838890184,273784618⟩,⟨807578155,344816364⟩⟩,⟨⟨605779157,1826904437⟩,⟨1718198146,1754901581⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 8 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q8_Head3.value JFz_TX2_Q8_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q8_Head3.source,
      JFz_TX2_Q8_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q8_Head3.value := by
    change ((325470336<2147483647 ∧ 1629824597<2147483647) ∧ (1027046303<2147483647 ∧ 1214659801<2147483647)) ∧
      ((80717226<2147483647 ∧ 350563441<2147483647) ∧ (332114538<2147483647 ∧ 213721355<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q8_Tail3.value := by
    change ((1513419848<2147483647 ∧ 791443668<2147483647) ∧ (1928015499<2147483647 ∧ 1277640210<2147483647)) ∧
      ((525061931<2147483647 ∧ 1476340996<2147483647) ∧ (1386083608<2147483647 ∧ 1541180226<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q8_Dot3
end
