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
namespace AspisR1.JFz_TX2_Q5_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1635235269#u32,1399699857#u32⟩,⟨2085231818#u32,142489239#u32⟩⟩,⟨⟨256429721#u32,2093575825#u32⟩,⟨1607583802#u32,1189554618#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 5 2 0 0 26%2147483647=1635235269 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*405717642+855639275*2133825538+867568255*56504066+352063*364003553+1106523000*784793207+1554033304*1901238265+1430280692*252914892+1491718280*1388501940+118514350*901724101+1675652887*1695155609+1364884909*1031325827+1135303194*1360638028+304762092*1288570666+1465393816*576945252+824208172*1434603534+1752653420*1782786976+1385409049*768608677+1003904973*1417879659+1298953245*618446725+2005758375*1435423595+497936241*1853300847+235809508*1534975197+1478307182*1498273614+1858903615*1780969212+628035096*221855252+1244951250*287947911)%2147483647=1635235269
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 5 2 1 0 26%2147483647=1399699857 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*405717642+1483149559*2133825538+655227887*56504066+39062738*364003553+729079828*784793207+67370206*1901238265+1685049618*252914892+385547620*1388501940+1786803209*901724101+779721715*1695155609+594709522*1031325827+338788461*1360638028+526756808*1288570666+184076238*576945252+1852498770*1434603534+2102463508*1782786976+1086671526*768608677+1147694576*1417879659+1504805752*618446725+2005073905*1435423595+185008025*1853300847+1485990146*1534975197+1255280192*1498273614+1018329259*1780969212+570157693*221855252+1511904630*287947911)%2147483647=1399699857
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 5 2 2 0 26%2147483647=2085231818 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*405717642+1898717401*2133825538+1032732628*56504066+1313565596*364003553+1074182998*784793207+1410213748*1901238265+1182702806*252914892+321711020*1388501940+2062791928*901724101+1188803754*1695155609+2038502201*1031325827+735931834*1360638028+1330533011*1288570666+1052874750*576945252+950153811*1434603534+1225424092*1782786976+1659116453*768608677+1474177753*1417879659+2073609211*618446725+1602919019*1435423595+1865917845*1853300847+1085624123*1534975197+1837870964*1498273614+1550509101*1780969212+1661725734*221855252+2066655336*287947911)%2147483647=2085231818
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 5 2 3 0 26%2147483647=142489239 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*405717642+1849775942*2133825538+656039795*56504066+1840648083*364003553+246996287*784793207+1369248953*1901238265+1132591724*252914892+92744917*1388501940+1719480363*901724101+1266677922*1695155609+377386917*1031325827+735227219*1360638028+465096431*1288570666+451889791*576945252+1379836302*1434603534+618598847*1782786976+1624084534*768608677+1511477847*1417879659+1840812326*618446725+185546252*1435423595+2145463598*1853300847+82870699*1534975197+1625323762*1498273614+1843639311*1780969212+1777269271*221855252+1645120956*287947911)%2147483647=142489239
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 5 2 4 0 26%2147483647=256429721 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*405717642+1112406525*2133825538+1345999435*56504066+752376469*364003553+634588140*784793207+1419170319*1901238265+1702860885*252914892+710076517*1388501940+1256487405*901724101+1114745059*1695155609+1137838899*1031325827+1254184109*1360638028+1038210451*1288570666+274378589*576945252+171986381*1434603534+1536678585*1782786976+1305878831*768608677+1335902916*1417879659+1755193245*618446725+2023391453*1435423595+293456010*1853300847+1751078325*1534975197+1423042536*1498273614+1749638204*1780969212+1345811362*221855252+1284924881*287947911)%2147483647=256429721
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 5 2 5 0 26%2147483647=2093575825 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*405717642+1796814865*2133825538+1253123171*56504066+1317611639*364003553+1559245386*784793207+1866942376*1901238265+1973593402*252914892+47019780*1388501940+1353487525*901724101+1840161555*1695155609+2003659556*1031325827+200559114*1360638028+334988447*1288570666+2023650872*576945252+1296497964*1434603534+34285357*1782786976+1685894190*768608677+995962325*1417879659+1295624230*618446725+1199631211*1435423595+1948677857*1853300847+1425322328*1534975197+1466877680*1498273614+702011012*1780969212+937706871*221855252+455802666*287947911)%2147483647=2093575825
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 5 2 6 0 26%2147483647=1607583802 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*405717642+1838939499*2133825538+1353876630*56504066+1258713036*364003553+1947503436*784793207+1271796599*1901238265+1660157177*252914892+564707688*1388501940+1858113864*901724101+1015817431*1695155609+1264608004*1031325827+735383960*1360638028+221696734*1288570666+1297524163*576945252+109088572*1434603534+792206628*1782786976+1921581249*768608677+94118806*1417879659+476103426*618446725+239612482*1435423595+177052717*1853300847+826458039*1534975197+1923715623*1498273614+1014161165*1780969212+1341609618*221855252+786325583*287947911)%2147483647=1607583802
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 5 2 7 0 26%2147483647=1189554618 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*405717642+418714188*2133825538+1675147475*56504066+1674326661*364003553+547797802*784793207+2073962627*1901238265+897270857*252914892+1582958967*1388501940+49892701*901724101+1256824732*1695155609+1435903714*1031325827+742583315*1360638028+1789294768*1288570666+13407412*576945252+518661610*1434603534+1259751297*1782786976+1695663205*768608677+2068940067*1417879659+940478841*618446725+1982757556*1435423595+1956713516*1853300847+863066484*1534975197+522298462*1498273614+1343575777*1780969212+771712139*221855252+157728743*287947911)%2147483647=1189554618
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 5 2
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
end AspisR1.JFz_TX2_Q5_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2442094182#u64 3150943286#u64 6227374711#u64 5186049708#u64⟩,⟨pack 2389252605#u64 1519975710#u64 4135072726#u64 2728005114#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 3294133101103492402#u64 2252090608695739203#u64 9626780688019345000#u64 7623894400342544268#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 69023417#u32 1007027658#u32 1670638743#u32 1995067252#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69023417#u32) (JFs_TX2_RawMath.extend 1007027658#u32) (JFs_TX2_RawMath.extend 1670638743#u32) (JFs_TX2_RawMath.extend 1995067252#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 69023417#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69023417#u32) (JFs_TX2_RawMath.extend 1007027658#u32) (JFs_TX2_RawMath.extend 1670638743#u32) (JFs_TX2_RawMath.extend 1995067252#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1007027658#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69023417#u32) (JFs_TX2_RawMath.extend 1007027658#u32) (JFs_TX2_RawMath.extend 1670638743#u32) (JFs_TX2_RawMath.extend 1995067252#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1670638743#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69023417#u32) (JFs_TX2_RawMath.extend 1007027658#u32) (JFs_TX2_RawMath.extend 1670638743#u32) (JFs_TX2_RawMath.extend 1995067252#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1995067252#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 3389390089742584149#u64 536244906754489681#u64 5528459573289427573#u64 5182452340195755030#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 69023417#u32 1007027658#u32 1670638743#u32 1995067252#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69023417#u32) (JFs_TX2_RawMath.extend 1007027658#u32) (JFs_TX2_RawMath.extend 1670638743#u32) (JFs_TX2_RawMath.extend 1995067252#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 69023417#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69023417#u32) (JFs_TX2_RawMath.extend 1007027658#u32) (JFs_TX2_RawMath.extend 1670638743#u32) (JFs_TX2_RawMath.extend 1995067252#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1007027658#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69023417#u32) (JFs_TX2_RawMath.extend 1007027658#u32) (JFs_TX2_RawMath.extend 1670638743#u32) (JFs_TX2_RawMath.extend 1995067252#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1670638743#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 69023417#u32) (JFs_TX2_RawMath.extend 1007027658#u32) (JFs_TX2_RawMath.extend 1670638743#u32) (JFs_TX2_RawMath.extend 1995067252#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1995067252#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails15.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value0_2=
      ok (.Ok (pack 69023417#u32 1007027658#u32 1670638743#u32 1995067252#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (69023417<2147483647 ∧ 1007027658<2147483647) ∧ (1670638743<2147483647 ∧ 1995067252<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 69023417#u32 1007027658#u32 1670638743#u32 1995067252#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 69023417#u32 1007027658#u32 1670638743#u32 1995067252#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q5_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2442094182#u64 3150943286#u64 6227374711#u64 5186049708#u64⟩,⟨pack 2389252605#u64 1519975710#u64 4135072726#u64 2728005114#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5299061277#u64 5164132195#u64 11332945299#u64 8868632704#u64⟩,⟨pack 6243031644#u64 3452740108#u64 9759310383#u64 4091138848#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 6091133320118780096#u64 2757157722435095167#u64 8644954275192945380#u64 6256338935112911770#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1016524396#u32 1251169994#u32 59818645#u32 1586340375#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1016524396#u32) (JFs_TX2_RawMath.extend 1251169994#u32) (JFs_TX2_RawMath.extend 59818645#u32) (JFs_TX2_RawMath.extend 1586340375#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1016524396#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1016524396#u32) (JFs_TX2_RawMath.extend 1251169994#u32) (JFs_TX2_RawMath.extend 59818645#u32) (JFs_TX2_RawMath.extend 1586340375#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1251169994#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1016524396#u32) (JFs_TX2_RawMath.extend 1251169994#u32) (JFs_TX2_RawMath.extend 59818645#u32) (JFs_TX2_RawMath.extend 1586340375#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 59818645#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1016524396#u32) (JFs_TX2_RawMath.extend 1251169994#u32) (JFs_TX2_RawMath.extend 59818645#u32) (JFs_TX2_RawMath.extend 1586340375#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1586340375#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4967199704511540415#u64 1050394331682972870#u64 8635059439865382075#u64 2192667161710030545#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1016524396#u32 1251169994#u32 59818645#u32 1586340375#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1016524396#u32) (JFs_TX2_RawMath.extend 1251169994#u32) (JFs_TX2_RawMath.extend 59818645#u32) (JFs_TX2_RawMath.extend 1586340375#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1016524396#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1016524396#u32) (JFs_TX2_RawMath.extend 1251169994#u32) (JFs_TX2_RawMath.extend 59818645#u32) (JFs_TX2_RawMath.extend 1586340375#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1251169994#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1016524396#u32) (JFs_TX2_RawMath.extend 1251169994#u32) (JFs_TX2_RawMath.extend 59818645#u32) (JFs_TX2_RawMath.extend 1586340375#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 59818645#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1016524396#u32) (JFs_TX2_RawMath.extend 1251169994#u32) (JFs_TX2_RawMath.extend 59818645#u32) (JFs_TX2_RawMath.extend 1586340375#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1586340375#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails15.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value1_2=
      ok (.Ok (pack 1016524396#u32 1251169994#u32 59818645#u32 1586340375#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1016524396<2147483647 ∧ 1251169994<2147483647) ∧ (59818645<2147483647 ∧ 1586340375<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 1016524396#u32 1251169994#u32 59818645#u32 1586340375#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2442094182#u64 3150943286#u64 6227374711#u64 5186049708#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 1016524396#u32 1251169994#u32 59818645#u32 1586340375#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2389252605#u64 1519975710#u64 4135072726#u64 2728005114#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q5_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 5299061277#u64 5164132195#u64 11332945299#u64 8868632704#u64⟩,⟨pack 6243031644#u64 3452740108#u64 9759310383#u64 4091138848#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9432856069#u64 5347643393#u64 15618137904#u64 10598448459#u64⟩,⟨pack 9110877395#u64 4784507643#u64 14194807745#u64 7035609391#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 4555167375413365433#u64 89946833047063624#u64 9178917147519662230#u64 799999544273571354#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 37827965#u32 134790195#u32 666619095#u32 559039834#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 37827965#u32) (JFs_TX2_RawMath.extend 134790195#u32) (JFs_TX2_RawMath.extend 666619095#u32) (JFs_TX2_RawMath.extend 559039834#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 37827965#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 37827965#u32) (JFs_TX2_RawMath.extend 134790195#u32) (JFs_TX2_RawMath.extend 666619095#u32) (JFs_TX2_RawMath.extend 559039834#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 134790195#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 37827965#u32) (JFs_TX2_RawMath.extend 134790195#u32) (JFs_TX2_RawMath.extend 666619095#u32) (JFs_TX2_RawMath.extend 559039834#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 666619095#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 37827965#u32) (JFs_TX2_RawMath.extend 134790195#u32) (JFs_TX2_RawMath.extend 666619095#u32) (JFs_TX2_RawMath.extend 559039834#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 559039834#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4429743409208271397#u64 309158410795644176#u64 9207419355939318612#u64 2580082352900568986#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 37827965#u32 134790195#u32 666619095#u32 559039834#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 37827965#u32) (JFs_TX2_RawMath.extend 134790195#u32) (JFs_TX2_RawMath.extend 666619095#u32) (JFs_TX2_RawMath.extend 559039834#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 37827965#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 37827965#u32) (JFs_TX2_RawMath.extend 134790195#u32) (JFs_TX2_RawMath.extend 666619095#u32) (JFs_TX2_RawMath.extend 559039834#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 134790195#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 37827965#u32) (JFs_TX2_RawMath.extend 134790195#u32) (JFs_TX2_RawMath.extend 666619095#u32) (JFs_TX2_RawMath.extend 559039834#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 666619095#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 37827965#u32) (JFs_TX2_RawMath.extend 134790195#u32) (JFs_TX2_RawMath.extend 666619095#u32) (JFs_TX2_RawMath.extend 559039834#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 559039834#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails15.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails15.value2_2=
      ok (.Ok (pack 37827965#u32 134790195#u32 666619095#u32 559039834#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (37827965<2147483647 ∧ 134790195<2147483647) ∧ (666619095<2147483647 ∧ 559039834<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 37827965#u32 134790195#u32 666619095#u32 559039834#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 5299061277#u64 5164132195#u64 11332945299#u64 8868632704#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 37827965#u32 134790195#u32 666619095#u32 559039834#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6243031644#u64 3452740108#u64 9759310383#u64 4091138848#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q5_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨842921481#u32,1052676099#u32⟩,⟨585752375#u32,2008513871#u32⟩⟩,⟨⟨520942807#u32,489540349#u32⟩,⟨1309905863#u32,593158450#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q5_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q5_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9432856069%2147483647 at h0
  norm_num at h0
  have e0 : a0=842921481#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=5347643393%2147483647 at h1
  norm_num at h1
  have e1 : a1=1052676099#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=15618137904%2147483647 at h2
  norm_num at h2
  have e2 : a2=585752375#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10598448459%2147483647 at h3
  norm_num at h3
  have e3 : a3=2008513871#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9110877395%2147483647 at h4
  norm_num at h4
  have e4 : a4=520942807#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=4784507643%2147483647 at h5
  norm_num at h5
  have e5 : a5=489540349#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14194807745%2147483647 at h6
  norm_num at h6
  have e6 : a6=1309905863#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=7035609391%2147483647 at h7
  norm_num at h7
  have e7 : a7=593158450#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q5_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails15.value0_2
      from JFr_TX2_Tails15.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails15.value1_2
      from JFr_TX2_Tails15.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 5))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails15.value2_2
      from JFr_TX2_Tails15.source2_2,
    JFz_TX2_Q5_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q5_Raw20.after=JFz_TX2_Q5_Raw21.before := rfl
  have same2 : JFz_TX2_Q5_Raw21.after=JFz_TX2_Q5_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q5_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q5_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q5_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q5_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨330673103#u32,304892309#u32⟩,⟨523500546#u32,3519463#u32⟩⟩,⟨⟨777372528#u32,435632527#u32⟩,⟨770006018#u32,1782713068#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((330673103<2147483647 ∧ 304892309<2147483647) ∧ (523500546<2147483647 ∧ 3519463<2147483647)) ∧
    ((777372528<2147483647 ∧ 435632527<2147483647) ∧ (770006018<2147483647 ∧ 1782713068<2147483647))
  omega
theorem addition : decode JFz_TX2_Q5_Head2.value+decode JFz_TX2_Q5_Tail2.value=decode value := by
  change (⟨⟨⟨1635235269,1399699857⟩,⟨2085231818,142489239⟩⟩,⟨⟨256429721,2093575825⟩,⟨1607583802,1189554618⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨842921481,1052676099⟩,⟨585752375,2008513871⟩⟩,⟨⟨520942807,489540349⟩,⟨1309905863,593158450⟩⟩⟩=⟨⟨⟨330673103,304892309⟩,⟨523500546,3519463⟩⟩,⟨⟨777372528,435632527⟩,⟨770006018,1782713068⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 5)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 5 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q5_Head2.value JFz_TX2_Q5_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q5_Head2.source,
      JFz_TX2_Q5_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q5_Head2.value := by
    change ((1635235269<2147483647 ∧ 1399699857<2147483647) ∧ (2085231818<2147483647 ∧ 142489239<2147483647)) ∧
      ((256429721<2147483647 ∧ 2093575825<2147483647) ∧ (1607583802<2147483647 ∧ 1189554618<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q5_Tail2.value := by
    change ((842921481<2147483647 ∧ 1052676099<2147483647) ∧ (585752375<2147483647 ∧ 2008513871<2147483647)) ∧
      ((520942807<2147483647 ∧ 489540349<2147483647) ∧ (1309905863<2147483647 ∧ 593158450<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q5_Dot2
end
