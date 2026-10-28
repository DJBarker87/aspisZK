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
namespace AspisR1.JFz_TX2_Q4_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨1469414672#u32,1571660719#u32⟩,⟨1914333643#u32,1177239331#u32⟩⟩,⟨⟨118313638#u32,1898374020#u32⟩,⟨104847145#u32,188562301#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 4 2 0 0 26%2147483647=1469414672 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1354284690+855639275*1392681657+867568255*634046277+352063*1294903711+1106523000*866962640+1554033304*261972796+1430280692*1038929156+1491718280*1067623136+118514350*1314892291+1675652887*1513910827+1364884909*1103072688+1135303194*2126577431+304762092*1684684026+1465393816*678480002+824208172*1760889866+1752653420*42639896+1385409049*1422688030+1003904973*2004143205+1298953245*808104275+2005758375*361126375+497936241*182126752+235809508*84047586+1478307182*326035697+1858903615*1858681232+628035096*1570988722+1244951250*1110958852)%2147483647=1469414672
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 4 2 1 0 26%2147483647=1571660719 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1354284690+1483149559*1392681657+655227887*634046277+39062738*1294903711+729079828*866962640+67370206*261972796+1685049618*1038929156+385547620*1067623136+1786803209*1314892291+779721715*1513910827+594709522*1103072688+338788461*2126577431+526756808*1684684026+184076238*678480002+1852498770*1760889866+2102463508*42639896+1086671526*1422688030+1147694576*2004143205+1504805752*808104275+2005073905*361126375+185008025*182126752+1485990146*84047586+1255280192*326035697+1018329259*1858681232+570157693*1570988722+1511904630*1110958852)%2147483647=1571660719
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 4 2 2 0 26%2147483647=1914333643 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1354284690+1898717401*1392681657+1032732628*634046277+1313565596*1294903711+1074182998*866962640+1410213748*261972796+1182702806*1038929156+321711020*1067623136+2062791928*1314892291+1188803754*1513910827+2038502201*1103072688+735931834*2126577431+1330533011*1684684026+1052874750*678480002+950153811*1760889866+1225424092*42639896+1659116453*1422688030+1474177753*2004143205+2073609211*808104275+1602919019*361126375+1865917845*182126752+1085624123*84047586+1837870964*326035697+1550509101*1858681232+1661725734*1570988722+2066655336*1110958852)%2147483647=1914333643
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 4 2 3 0 26%2147483647=1177239331 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1354284690+1849775942*1392681657+656039795*634046277+1840648083*1294903711+246996287*866962640+1369248953*261972796+1132591724*1038929156+92744917*1067623136+1719480363*1314892291+1266677922*1513910827+377386917*1103072688+735227219*2126577431+465096431*1684684026+451889791*678480002+1379836302*1760889866+618598847*42639896+1624084534*1422688030+1511477847*2004143205+1840812326*808104275+185546252*361126375+2145463598*182126752+82870699*84047586+1625323762*326035697+1843639311*1858681232+1777269271*1570988722+1645120956*1110958852)%2147483647=1177239331
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 4 2 4 0 26%2147483647=118313638 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1354284690+1112406525*1392681657+1345999435*634046277+752376469*1294903711+634588140*866962640+1419170319*261972796+1702860885*1038929156+710076517*1067623136+1256487405*1314892291+1114745059*1513910827+1137838899*1103072688+1254184109*2126577431+1038210451*1684684026+274378589*678480002+171986381*1760889866+1536678585*42639896+1305878831*1422688030+1335902916*2004143205+1755193245*808104275+2023391453*361126375+293456010*182126752+1751078325*84047586+1423042536*326035697+1749638204*1858681232+1345811362*1570988722+1284924881*1110958852)%2147483647=118313638
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 4 2 5 0 26%2147483647=1898374020 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1354284690+1796814865*1392681657+1253123171*634046277+1317611639*1294903711+1559245386*866962640+1866942376*261972796+1973593402*1038929156+47019780*1067623136+1353487525*1314892291+1840161555*1513910827+2003659556*1103072688+200559114*2126577431+334988447*1684684026+2023650872*678480002+1296497964*1760889866+34285357*42639896+1685894190*1422688030+995962325*2004143205+1295624230*808104275+1199631211*361126375+1948677857*182126752+1425322328*84047586+1466877680*326035697+702011012*1858681232+937706871*1570988722+455802666*1110958852)%2147483647=1898374020
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 4 2 6 0 26%2147483647=104847145 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1354284690+1838939499*1392681657+1353876630*634046277+1258713036*1294903711+1947503436*866962640+1271796599*261972796+1660157177*1038929156+564707688*1067623136+1858113864*1314892291+1015817431*1513910827+1264608004*1103072688+735383960*2126577431+221696734*1684684026+1297524163*678480002+109088572*1760889866+792206628*42639896+1921581249*1422688030+94118806*2004143205+476103426*808104275+239612482*361126375+177052717*182126752+826458039*84047586+1923715623*326035697+1014161165*1858681232+1341609618*1570988722+786325583*1110958852)%2147483647=104847145
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 4 2 7 0 26%2147483647=188562301 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1354284690+418714188*1392681657+1675147475*634046277+1674326661*1294903711+547797802*866962640+2073962627*261972796+897270857*1038929156+1582958967*1067623136+49892701*1314892291+1256824732*1513910827+1435903714*1103072688+742583315*2126577431+1789294768*1684684026+13407412*678480002+518661610*1760889866+1259751297*42639896+1695663205*1422688030+2068940067*2004143205+940478841*808104275+1982757556*361126375+1956713516*182126752+863066484*84047586+522298462*326035697+1343575777*1858681232+771712139*1570988722+157728743*1110958852)%2147483647=188562301
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 4 2
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
end AspisR1.JFz_TX2_Q4_Head2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw20
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2010766444#u64 3386796039#u64 7070866212#u64 3751117543#u64⟩,⟨pack 2324560853#u64 1622357695#u64 4241819278#u64 5451144207#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 4192307484511025544#u64 5715781583919207909#u64 12157972700261860258#u64 7292939992499359318#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1110377653#u32 1919068331#u32 1949538169#u32 1107493961#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1110377653#u32) (JFs_TX2_RawMath.extend 1919068331#u32) (JFs_TX2_RawMath.extend 1949538169#u32) (JFs_TX2_RawMath.extend 1107493961#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1110377653#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1110377653#u32) (JFs_TX2_RawMath.extend 1919068331#u32) (JFs_TX2_RawMath.extend 1949538169#u32) (JFs_TX2_RawMath.extend 1107493961#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1919068331#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1110377653#u32) (JFs_TX2_RawMath.extend 1919068331#u32) (JFs_TX2_RawMath.extend 1949538169#u32) (JFs_TX2_RawMath.extend 1107493961#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1949538169#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1110377653#u32) (JFs_TX2_RawMath.extend 1919068331#u32) (JFs_TX2_RawMath.extend 1949538169#u32) (JFs_TX2_RawMath.extend 1107493961#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1107493961#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2720131885594200258#u64 2239997231250215813#u64 6992572361522270087#u64 9177506425875710239#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1110377653#u32 1919068331#u32 1949538169#u32 1107493961#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1110377653#u32) (JFs_TX2_RawMath.extend 1919068331#u32) (JFs_TX2_RawMath.extend 1949538169#u32) (JFs_TX2_RawMath.extend 1107493961#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1110377653#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1110377653#u32) (JFs_TX2_RawMath.extend 1919068331#u32) (JFs_TX2_RawMath.extend 1949538169#u32) (JFs_TX2_RawMath.extend 1107493961#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1919068331#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1110377653#u32) (JFs_TX2_RawMath.extend 1919068331#u32) (JFs_TX2_RawMath.extend 1949538169#u32) (JFs_TX2_RawMath.extend 1107493961#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1949538169#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1110377653#u32) (JFs_TX2_RawMath.extend 1919068331#u32) (JFs_TX2_RawMath.extend 1949538169#u32) (JFs_TX2_RawMath.extend 1107493961#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1107493961#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails14.value0_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value0_2=
      ok (.Ok (pack 1110377653#u32 1919068331#u32 1949538169#u32 1107493961#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1110377653<2147483647 ∧ 1919068331<2147483647) ∧ (1949538169<2147483647 ∧ 1107493961<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 1110377653#u32 1919068331#u32 1949538169#u32 1107493961#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 1110377653#u32 1919068331#u32 1949538169#u32 1107493961#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q4_Raw20
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw21
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2010766444#u64 3386796039#u64 7070866212#u64 3751117543#u64⟩,⟨pack 2324560853#u64 1622357695#u64 4241819278#u64 5451144207#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4829709814#u64 5592691839#u64 12811293693#u64 5620749476#u64⟩,⟨pack 6021525985#u64 2959066925#u64 8996441032#u64 6203768164#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 5846222160284205409#u64 2554718540918877828#u64 11180658225531100675#u64 3337624431123829316#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 872934737#u32 1172552440#u32 1145841527#u32 7078652#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872934737#u32) (JFs_TX2_RawMath.extend 1172552440#u32) (JFs_TX2_RawMath.extend 1145841527#u32) (JFs_TX2_RawMath.extend 7078652#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 872934737#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872934737#u32) (JFs_TX2_RawMath.extend 1172552440#u32) (JFs_TX2_RawMath.extend 1145841527#u32) (JFs_TX2_RawMath.extend 7078652#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1172552440#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872934737#u32) (JFs_TX2_RawMath.extend 1172552440#u32) (JFs_TX2_RawMath.extend 1145841527#u32) (JFs_TX2_RawMath.extend 7078652#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1145841527#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872934737#u32) (JFs_TX2_RawMath.extend 1172552440#u32) (JFs_TX2_RawMath.extend 1145841527#u32) (JFs_TX2_RawMath.extend 7078652#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 7078652#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4893461889080169146#u64 965283891241930563#u64 9692703585491417117#u64 1316625559770427748#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 872934737#u32 1172552440#u32 1145841527#u32 7078652#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872934737#u32) (JFs_TX2_RawMath.extend 1172552440#u32) (JFs_TX2_RawMath.extend 1145841527#u32) (JFs_TX2_RawMath.extend 7078652#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 872934737#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872934737#u32) (JFs_TX2_RawMath.extend 1172552440#u32) (JFs_TX2_RawMath.extend 1145841527#u32) (JFs_TX2_RawMath.extend 7078652#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1172552440#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872934737#u32) (JFs_TX2_RawMath.extend 1172552440#u32) (JFs_TX2_RawMath.extend 1145841527#u32) (JFs_TX2_RawMath.extend 7078652#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1145841527#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 872934737#u32) (JFs_TX2_RawMath.extend 1172552440#u32) (JFs_TX2_RawMath.extend 1145841527#u32) (JFs_TX2_RawMath.extend 7078652#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 7078652#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails14.value1_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value1_2=
      ok (.Ok (pack 872934737#u32 1172552440#u32 1145841527#u32 7078652#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (872934737<2147483647 ∧ 1172552440<2147483647) ∧ (1145841527<2147483647 ∧ 7078652<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 872934737#u32 1172552440#u32 1145841527#u32 7078652#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2010766444#u64 3386796039#u64 7070866212#u64 3751117543#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 872934737#u32 1172552440#u32 1145841527#u32 7078652#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2324560853#u64 1622357695#u64 4241819278#u64 5451144207#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q4_Raw21
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Raw22
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 4829709814#u64 5592691839#u64 12811293693#u64 5620749476#u64⟩,⟨pack 6021525985#u64 2959066925#u64 8996441032#u64 6203768164#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9506761794#u64 7901127657#u64 19466264073#u64 7904393359#u64⟩,⟨pack 9716542123#u64 5905065154#u64 15032089397#u64 12131397780#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 5476242851824605845#u64 1359100234505843326#u64 10264325612093464199#u64 3791285222459502662#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2092340541#u32 358352816#u32 1499822090#u32 2119554867#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2092340541#u32) (JFs_TX2_RawMath.extend 358352816#u32) (JFs_TX2_RawMath.extend 1499822090#u32) (JFs_TX2_RawMath.extend 2119554867#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2092340541#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2092340541#u32) (JFs_TX2_RawMath.extend 358352816#u32) (JFs_TX2_RawMath.extend 1499822090#u32) (JFs_TX2_RawMath.extend 2119554867#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 358352816#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2092340541#u32) (JFs_TX2_RawMath.extend 358352816#u32) (JFs_TX2_RawMath.extend 1499822090#u32) (JFs_TX2_RawMath.extend 2119554867#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1499822090#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2092340541#u32) (JFs_TX2_RawMath.extend 358352816#u32) (JFs_TX2_RawMath.extend 1499822090#u32) (JFs_TX2_RawMath.extend 2119554867#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2119554867#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 7663383444844043138#u64 4502650953695959862#u64 11763465913024658325#u64 11123680586153194003#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2092340541#u32 358352816#u32 1499822090#u32 2119554867#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2092340541#u32) (JFs_TX2_RawMath.extend 358352816#u32) (JFs_TX2_RawMath.extend 1499822090#u32) (JFs_TX2_RawMath.extend 2119554867#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2092340541#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2092340541#u32) (JFs_TX2_RawMath.extend 358352816#u32) (JFs_TX2_RawMath.extend 1499822090#u32) (JFs_TX2_RawMath.extend 2119554867#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 358352816#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2092340541#u32) (JFs_TX2_RawMath.extend 358352816#u32) (JFs_TX2_RawMath.extend 1499822090#u32) (JFs_TX2_RawMath.extend 2119554867#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1499822090#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2092340541#u32) (JFs_TX2_RawMath.extend 358352816#u32) (JFs_TX2_RawMath.extend 1499822090#u32) (JFs_TX2_RawMath.extend 2119554867#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2119554867#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails14.value2_2=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails14.value2_2=
      ok (.Ok (pack 2092340541#u32 358352816#u32 1499822090#u32 2119554867#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (2092340541<2147483647 ∧ 358352816<2147483647) ∧ (1499822090<2147483647 ∧ 2119554867<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 2092340541#u32 358352816#u32 1499822090#u32 2119554867#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 4829709814#u64 5592691839#u64 12811293693#u64 5620749476#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 2092340541#u32 358352816#u32 1499822090#u32 2119554867#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6021525985#u64 2959066925#u64 8996441032#u64 6203768164#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q4_Raw22
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Tail2
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨916827206#u32,1458676716#u32⟩,⟨138911250#u32,1461942418#u32⟩⟩,⟨⟨1126607535#u32,1610097860#u32⟩,⟨2147187515#u32,1393979545#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q4_Raw22.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q4_Raw22.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9506761794%2147483647 at h0
  norm_num at h0
  have e0 : a0=916827206#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=7901127657%2147483647 at h1
  norm_num at h1
  have e1 : a1=1458676716#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=19466264073%2147483647 at h2
  norm_num at h2
  have e2 : a2=138911250#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=7904393359%2147483647 at h3
  norm_num at h3
  have e3 : a3=1461942418#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=9716542123%2147483647 at h4
  norm_num at h4
  have e4 : a4=1126607535#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5905065154%2147483647 at h5
  norm_num at h5
  have e5 : a5=1610097860#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=15032089397%2147483647 at h6
  norm_num at h6
  have e6 : a6=2147187515#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=12131397780%2147483647 at h7
  norm_num at h7
  have e7 : a7=1393979545#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (2:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q4_Raw20.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 2 0) (JFr_TX2_Tails.stop 2 0)=ok JFr_TX2_Tails14.value0_2
      from JFr_TX2_Tails14.source0_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 2 1) (JFr_TX2_Tails.stop 2 1)=ok JFr_TX2_Tails14.value1_2
      from JFr_TX2_Tails14.source1_2,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 4))
      (JFr_TX2_Tails.offset 2 2) (JFr_TX2_Tails.stop 2 2)=ok JFr_TX2_Tails14.value2_2
      from JFr_TX2_Tails14.source2_2,
    JFz_TX2_Q4_Raw20.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q4_Raw20.after=JFz_TX2_Q4_Raw21.before := rfl
  have same2 : JFz_TX2_Q4_Raw21.after=JFz_TX2_Q4_Raw22.before := rfl
  simp only [same1,JFz_TX2_Q4_Raw21.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q4_Raw22.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q4_Tail2
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q4_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨238758231#u32,882853788#u32⟩,⟨2053244893#u32,491698102#u32⟩⟩,⟨⟨1244921173#u32,1360988233#u32⟩,⟨104551013#u32,1582541846#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((238758231<2147483647 ∧ 882853788<2147483647) ∧ (2053244893<2147483647 ∧ 491698102<2147483647)) ∧
    ((1244921173<2147483647 ∧ 1360988233<2147483647) ∧ (104551013<2147483647 ∧ 1582541846<2147483647))
  omega
theorem addition : decode JFz_TX2_Q4_Head2.value+decode JFz_TX2_Q4_Tail2.value=decode value := by
  change (⟨⟨⟨1469414672,1571660719⟩,⟨1914333643,1177239331⟩⟩,⟨⟨118313638,1898374020⟩,⟨104847145,188562301⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨916827206,1458676716⟩,⟨138911250,1461942418⟩⟩,⟨⟨1126607535,1610097860⟩,⟨2147187515,1393979545⟩⟩⟩=⟨⟨⟨238758231,882853788⟩,⟨2053244893,491698102⟩⟩,⟨⟨1244921173,1360988233⟩,⟨104551013,1582541846⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 4)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 4 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q4_Head2.value JFz_TX2_Q4_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q4_Head2.source,
      JFz_TX2_Q4_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q4_Head2.value := by
    change ((1469414672<2147483647 ∧ 1571660719<2147483647) ∧ (1914333643<2147483647 ∧ 1177239331<2147483647)) ∧
      ((118313638<2147483647 ∧ 1898374020<2147483647) ∧ (104847145<2147483647 ∧ 188562301<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q4_Tail2.value := by
    change ((916827206<2147483647 ∧ 1458676716<2147483647) ∧ (138911250<2147483647 ∧ 1461942418<2147483647)) ∧
      ((1126607535<2147483647 ∧ 1610097860<2147483647) ∧ (2147187515<2147483647 ∧ 1393979545<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q4_Dot2
end
