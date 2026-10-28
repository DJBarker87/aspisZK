import NDO_JFz_TX2_HeadTransport
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
import NDO_JFw_TX2_FoldPush
import NDO_JFw_TX2_P28
import NDO_JFr_TX2_Tails13
import NDO_JFw_TX2_PowerReads
import NDO_JFv_TX2_EbyKFinishMeaning
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨2077578132#u32,500816962#u32⟩,⟨26651211#u32,801021326#u32⟩⟩,⟨⟨338101642#u32,1824432091#u32⟩,⟨1482313683#u32,1565101116#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 3 1 0 0 26%2147483647=2077578132 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*892351705+855639275*1163812483+867568255*951171010+352063*296366373+1106523000*1654506829+1554033304*628743725+1430280692*650300407+1491718280*1502069148+118514350*605172618+1675652887*272870726+1364884909*934656572+1135303194*1042594502+304762092*766119187+1465393816*1231791269+824208172*1121291677+1752653420*730289405+1385409049*1904771140+1003904973*2071779747+1298953245*701578527+2005758375*1510116023+497936241*1727492022+235809508*312178444+1478307182*27307425+1858903615*1124119989+628035096*720345705+1244951250*385104159)%2147483647=2077578132
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 3 1 1 0 26%2147483647=500816962 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*892351705+1483149559*1163812483+655227887*951171010+39062738*296366373+729079828*1654506829+67370206*628743725+1685049618*650300407+385547620*1502069148+1786803209*605172618+779721715*272870726+594709522*934656572+338788461*1042594502+526756808*766119187+184076238*1231791269+1852498770*1121291677+2102463508*730289405+1086671526*1904771140+1147694576*2071779747+1504805752*701578527+2005073905*1510116023+185008025*1727492022+1485990146*312178444+1255280192*27307425+1018329259*1124119989+570157693*720345705+1511904630*385104159)%2147483647=500816962
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 3 1 2 0 26%2147483647=26651211 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*892351705+1898717401*1163812483+1032732628*951171010+1313565596*296366373+1074182998*1654506829+1410213748*628743725+1182702806*650300407+321711020*1502069148+2062791928*605172618+1188803754*272870726+2038502201*934656572+735931834*1042594502+1330533011*766119187+1052874750*1231791269+950153811*1121291677+1225424092*730289405+1659116453*1904771140+1474177753*2071779747+2073609211*701578527+1602919019*1510116023+1865917845*1727492022+1085624123*312178444+1837870964*27307425+1550509101*1124119989+1661725734*720345705+2066655336*385104159)%2147483647=26651211
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 3 1 3 0 26%2147483647=801021326 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*892351705+1849775942*1163812483+656039795*951171010+1840648083*296366373+246996287*1654506829+1369248953*628743725+1132591724*650300407+92744917*1502069148+1719480363*605172618+1266677922*272870726+377386917*934656572+735227219*1042594502+465096431*766119187+451889791*1231791269+1379836302*1121291677+618598847*730289405+1624084534*1904771140+1511477847*2071779747+1840812326*701578527+185546252*1510116023+2145463598*1727492022+82870699*312178444+1625323762*27307425+1843639311*1124119989+1777269271*720345705+1645120956*385104159)%2147483647=801021326
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 3 1 4 0 26%2147483647=338101642 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*892351705+1112406525*1163812483+1345999435*951171010+752376469*296366373+634588140*1654506829+1419170319*628743725+1702860885*650300407+710076517*1502069148+1256487405*605172618+1114745059*272870726+1137838899*934656572+1254184109*1042594502+1038210451*766119187+274378589*1231791269+171986381*1121291677+1536678585*730289405+1305878831*1904771140+1335902916*2071779747+1755193245*701578527+2023391453*1510116023+293456010*1727492022+1751078325*312178444+1423042536*27307425+1749638204*1124119989+1345811362*720345705+1284924881*385104159)%2147483647=338101642
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 3 1 5 0 26%2147483647=1824432091 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*892351705+1796814865*1163812483+1253123171*951171010+1317611639*296366373+1559245386*1654506829+1866942376*628743725+1973593402*650300407+47019780*1502069148+1353487525*605172618+1840161555*272870726+2003659556*934656572+200559114*1042594502+334988447*766119187+2023650872*1231791269+1296497964*1121291677+34285357*730289405+1685894190*1904771140+995962325*2071779747+1295624230*701578527+1199631211*1510116023+1948677857*1727492022+1425322328*312178444+1466877680*27307425+702011012*1124119989+937706871*720345705+455802666*385104159)%2147483647=1824432091
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 3 1 6 0 26%2147483647=1482313683 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*892351705+1838939499*1163812483+1353876630*951171010+1258713036*296366373+1947503436*1654506829+1271796599*628743725+1660157177*650300407+564707688*1502069148+1858113864*605172618+1015817431*272870726+1264608004*934656572+735383960*1042594502+221696734*766119187+1297524163*1231791269+109088572*1121291677+792206628*730289405+1921581249*1904771140+94118806*2071779747+476103426*701578527+239612482*1510116023+177052717*1727492022+826458039*312178444+1923715623*27307425+1014161165*1124119989+1341609618*720345705+786325583*385104159)%2147483647=1482313683
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 3 1 7 0 26%2147483647=1565101116 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*892351705+418714188*1163812483+1675147475*951171010+1674326661*296366373+547797802*1654506829+2073962627*628743725+897270857*650300407+1582958967*1502069148+49892701*605172618+1256824732*272870726+1435903714*934656572+742583315*1042594502+1789294768*766119187+13407412*1231791269+518661610*1121291677+1259751297*730289405+1695663205*1904771140+2068940067*2071779747+940478841*701578527+1982757556*1510116023+1956713516*1727492022+863066484*312178444+522298462*27307425+1343575777*1124119989+771712139*720345705+157728743*385104159)%2147483647=1565101116
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 3 1
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
end AspisR1.JFz_TX2_Q3_Head1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw10
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 1929872159#u64 3282967956#u64 6522557576#u64 2820863609#u64⟩,⟨pack 3067014604#u64 974312837#u64 4623804009#u64 3097665721#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 2466526891261151448#u64 3584345004072620032#u64 9465310946219999289#u64 3056216210024643987#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 94445204#u32 1613240695#u32 559072933#u32 354384152#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94445204#u32) (JFs_TX2_RawMath.extend 1613240695#u32) (JFs_TX2_RawMath.extend 559072933#u32) (JFs_TX2_RawMath.extend 354384152#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 94445204#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94445204#u32) (JFs_TX2_RawMath.extend 1613240695#u32) (JFs_TX2_RawMath.extend 559072933#u32) (JFs_TX2_RawMath.extend 354384152#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1613240695#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94445204#u32) (JFs_TX2_RawMath.extend 1613240695#u32) (JFs_TX2_RawMath.extend 559072933#u32) (JFs_TX2_RawMath.extend 354384152#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 559072933#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94445204#u32) (JFs_TX2_RawMath.extend 1613240695#u32) (JFs_TX2_RawMath.extend 559072933#u32) (JFs_TX2_RawMath.extend 354384152#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 354384152#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2646376251242793841#u64 838983595846106944#u64 5860457599256795172#u64 4362966430477050629#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 94445204#u32 1613240695#u32 559072933#u32 354384152#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94445204#u32) (JFs_TX2_RawMath.extend 1613240695#u32) (JFs_TX2_RawMath.extend 559072933#u32) (JFs_TX2_RawMath.extend 354384152#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 94445204#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94445204#u32) (JFs_TX2_RawMath.extend 1613240695#u32) (JFs_TX2_RawMath.extend 559072933#u32) (JFs_TX2_RawMath.extend 354384152#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1613240695#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94445204#u32) (JFs_TX2_RawMath.extend 1613240695#u32) (JFs_TX2_RawMath.extend 559072933#u32) (JFs_TX2_RawMath.extend 354384152#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 559072933#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 94445204#u32) (JFs_TX2_RawMath.extend 1613240695#u32) (JFs_TX2_RawMath.extend 559072933#u32) (JFs_TX2_RawMath.extend 354384152#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 354384152#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails13.value0_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value0_1=
      ok (.Ok (pack 94445204#u32 1613240695#u32 559072933#u32 354384152#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (94445204<2147483647 ∧ 1613240695<2147483647) ∧ (559072933<2147483647 ∧ 354384152<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 94445204#u32 1613240695#u32 559072933#u32 354384152#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 94445204#u32 1613240695#u32 559072933#u32 354384152#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q3_Raw10
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw11
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 1929872159#u64 3282967956#u64 6522557576#u64 2820863609#u64⟩,⟨pack 3067014604#u64 974312837#u64 4623804009#u64 3097665721#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5941549568#u64 5373264514#u64 10750437935#u64 7427951618#u64⟩,⟨pack 5204265166#u64 2863876934#u64 8460167751#u64 6052773391#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5048682439044254470#u64 4002284379018720270#u64 7133834331876713625#u64 6339872229532308770#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 610128754#u32 1982466907#u32 41744257#u32 1336533237#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 610128754#u32) (JFs_TX2_RawMath.extend 1982466907#u32) (JFs_TX2_RawMath.extend 41744257#u32) (JFs_TX2_RawMath.extend 1336533237#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 610128754#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 610128754#u32) (JFs_TX2_RawMath.extend 1982466907#u32) (JFs_TX2_RawMath.extend 41744257#u32) (JFs_TX2_RawMath.extend 1336533237#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1982466907#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 610128754#u32) (JFs_TX2_RawMath.extend 1982466907#u32) (JFs_TX2_RawMath.extend 41744257#u32) (JFs_TX2_RawMath.extend 1336533237#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 41744257#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 610128754#u32) (JFs_TX2_RawMath.extend 1982466907#u32) (JFs_TX2_RawMath.extend 41744257#u32) (JFs_TX2_RawMath.extend 1336533237#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1336533237#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4529867114804754106#u64 1424500246533555943#u64 8079042627282745072#u64 2131610816636083162#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 610128754#u32 1982466907#u32 41744257#u32 1336533237#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 610128754#u32) (JFs_TX2_RawMath.extend 1982466907#u32) (JFs_TX2_RawMath.extend 41744257#u32) (JFs_TX2_RawMath.extend 1336533237#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 610128754#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 610128754#u32) (JFs_TX2_RawMath.extend 1982466907#u32) (JFs_TX2_RawMath.extend 41744257#u32) (JFs_TX2_RawMath.extend 1336533237#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1982466907#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 610128754#u32) (JFs_TX2_RawMath.extend 1982466907#u32) (JFs_TX2_RawMath.extend 41744257#u32) (JFs_TX2_RawMath.extend 1336533237#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 41744257#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 610128754#u32) (JFs_TX2_RawMath.extend 1982466907#u32) (JFs_TX2_RawMath.extend 41744257#u32) (JFs_TX2_RawMath.extend 1336533237#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1336533237#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails13.value1_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value1_1=
      ok (.Ok (pack 610128754#u32 1982466907#u32 41744257#u32 1336533237#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (610128754<2147483647 ∧ 1982466907<2147483647) ∧ (41744257<2147483647 ∧ 1336533237<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 610128754#u32 1982466907#u32 41744257#u32 1336533237#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 1929872159#u64 3282967956#u64 6522557576#u64 2820863609#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 610128754#u32 1982466907#u32 41744257#u32 1336533237#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3067014604#u64 974312837#u64 4623804009#u64 3097665721#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q3_Raw11
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Raw12
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5941549568#u64 5373264514#u64 10750437935#u64 7427951618#u64⟩,⟨pack 5204265166#u64 2863876934#u64 8460167751#u64 6052773391#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 8508239491#u64 6844842200#u64 17210779977#u64 9216844837#u64⟩,⟨pack 8905073459#u64 5153772198#u64 12771352899#u64 10329436608#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4851048660719881831#u64 746949183889152432#u64 9274493821392371999#u64 2738168018241617287#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 941279730#u32 427218682#u32 1274925281#u32 1884210120#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 941279730#u32) (JFs_TX2_RawMath.extend 427218682#u32) (JFs_TX2_RawMath.extend 1274925281#u32) (JFs_TX2_RawMath.extend 1884210120#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 941279730#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 941279730#u32) (JFs_TX2_RawMath.extend 427218682#u32) (JFs_TX2_RawMath.extend 1274925281#u32) (JFs_TX2_RawMath.extend 1884210120#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 427218682#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 941279730#u32) (JFs_TX2_RawMath.extend 427218682#u32) (JFs_TX2_RawMath.extend 1274925281#u32) (JFs_TX2_RawMath.extend 1884210120#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1274925281#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 941279730#u32) (JFs_TX2_RawMath.extend 427218682#u32) (JFs_TX2_RawMath.extend 1274925281#u32) (JFs_TX2_RawMath.extend 1884210120#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1884210120#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 5492979786489782879#u64 2497768425735672084#u64 9224945618398234792#u64 8331115484421066984#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 941279730#u32 427218682#u32 1274925281#u32 1884210120#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 941279730#u32) (JFs_TX2_RawMath.extend 427218682#u32) (JFs_TX2_RawMath.extend 1274925281#u32) (JFs_TX2_RawMath.extend 1884210120#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 941279730#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 941279730#u32) (JFs_TX2_RawMath.extend 427218682#u32) (JFs_TX2_RawMath.extend 1274925281#u32) (JFs_TX2_RawMath.extend 1884210120#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 427218682#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 941279730#u32) (JFs_TX2_RawMath.extend 427218682#u32) (JFs_TX2_RawMath.extend 1274925281#u32) (JFs_TX2_RawMath.extend 1884210120#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1274925281#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 941279730#u32) (JFs_TX2_RawMath.extend 427218682#u32) (JFs_TX2_RawMath.extend 1274925281#u32) (JFs_TX2_RawMath.extend 1884210120#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1884210120#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails13.value2_1=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails13.value2_1=
      ok (.Ok (pack 941279730#u32 427218682#u32 1274925281#u32 1884210120#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (941279730<2147483647 ∧ 427218682<2147483647) ∧ (1274925281<2147483647 ∧ 1884210120<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 941279730#u32 427218682#u32 1274925281#u32 1884210120#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5941549568#u64 5373264514#u64 10750437935#u64 7427951618#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 941279730#u32 427218682#u32 1274925281#u32 1884210120#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5204265166#u64 2863876934#u64 8460167751#u64 6052773391#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q3_Raw12
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Tail1
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨2065788550#u32,402391259#u32⟩,⟨30910801#u32,626910249#u32⟩⟩,⟨⟨315138871#u32,858804904#u32⟩,⟨2033934664#u32,1739502020#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q3_Raw12.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q3_Raw12.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=8508239491%2147483647 at h0
  norm_num at h0
  have e0 : a0=2065788550#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6844842200%2147483647 at h1
  norm_num at h1
  have e1 : a1=402391259#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=17210779977%2147483647 at h2
  norm_num at h2
  have e2 : a2=30910801#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=9216844837%2147483647 at h3
  norm_num at h3
  have e3 : a3=626910249#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=8905073459%2147483647 at h4
  norm_num at h4
  have e4 : a4=315138871#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5153772198%2147483647 at h5
  norm_num at h5
  have e5 : a5=858804904#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=12771352899%2147483647 at h6
  norm_num at h6
  have e6 : a6=2033934664#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=10329436608%2147483647 at h7
  norm_num at h7
  have e7 : a7=1739502020#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (1:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q3_Raw10.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 1 0) (JFr_TX2_Tails.stop 1 0)=ok JFr_TX2_Tails13.value0_1
      from JFr_TX2_Tails13.source0_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 1 1) (JFr_TX2_Tails.stop 1 1)=ok JFr_TX2_Tails13.value1_1
      from JFr_TX2_Tails13.source1_1,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 3))
      (JFr_TX2_Tails.offset 1 2) (JFr_TX2_Tails.stop 1 2)=ok JFr_TX2_Tails13.value2_1
      from JFr_TX2_Tails13.source2_1,
    JFz_TX2_Q3_Raw10.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q3_Raw10.after=JFz_TX2_Q3_Raw11.before := rfl
  have same2 : JFz_TX2_Q3_Raw11.after=JFz_TX2_Q3_Raw12.before := rfl
  simp only [same1,JFz_TX2_Q3_Raw11.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q3_Raw12.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q3_Tail1
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q3_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1995883035#u32,903208221#u32⟩,⟨57562012#u32,1427931575#u32⟩⟩,⟨⟨653240513#u32,535753348#u32⟩,⟨1368764700#u32,1157119489#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1995883035<2147483647 ∧ 903208221<2147483647) ∧ (57562012<2147483647 ∧ 1427931575<2147483647)) ∧
    ((653240513<2147483647 ∧ 535753348<2147483647) ∧ (1368764700<2147483647 ∧ 1157119489<2147483647))
  omega
theorem addition : decode JFz_TX2_Q3_Head1.value+decode JFz_TX2_Q3_Tail1.value=decode value := by
  change (⟨⟨⟨2077578132,500816962⟩,⟨26651211,801021326⟩⟩,⟨⟨338101642,1824432091⟩,⟨1482313683,1565101116⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨2065788550,402391259⟩,⟨30910801,626910249⟩⟩,⟨⟨315138871,858804904⟩,⟨2033934664,1739502020⟩⟩⟩=⟨⟨⟨1995883035,903208221⟩,⟨57562012,1427931575⟩⟩,⟨⟨653240513,535753348⟩,⟨1368764700,1157119489⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 3)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 3 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q3_Head1.value JFz_TX2_Q3_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q3_Head1.source,
      JFz_TX2_Q3_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q3_Head1.value := by
    change ((2077578132<2147483647 ∧ 500816962<2147483647) ∧ (26651211<2147483647 ∧ 801021326<2147483647)) ∧
      ((338101642<2147483647 ∧ 1824432091<2147483647) ∧ (1482313683<2147483647 ∧ 1565101116<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q3_Tail1.value := by
    change ((2065788550<2147483647 ∧ 402391259<2147483647) ∧ (30910801<2147483647 ∧ 626910249<2147483647)) ∧
      ((315138871<2147483647 ∧ 858804904<2147483647) ∧ (2033934664<2147483647 ∧ 1739502020<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q3_Dot1
end
