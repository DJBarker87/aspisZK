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
namespace AspisR1.JFz_TX2_Q8_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨357341688#u32,486849109#u32⟩,⟨1755038724#u32,1456807269#u32⟩⟩,⟨⟨748974773#u32,1782476420#u32⟩,⟨2066500345#u32,1737870698#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 8 0 0 0 26%2147483647=357341688 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+1*1441901729+855639275*399835360+867568255*631199233+352063*960487500+1106523000*1991798734+1554033304*636832731+1430280692*729538841+1491718280*429217738+118514350*1977199940+1675652887*1772669964+1364884909*2102866707+1135303194*1766067030+304762092*1811189043+1465393816*1769320897+824208172*1149560869+1752653420*1084615208+1385409049*1498576196+1003904973*1130336214+1298953245*1089519845+2005758375*1436775260+497936241*1865493391+235809508*1046759287+1478307182*335259495+1858903615*1215521203+628035096*1959486198+1244951250*1861395891)%2147483647=357341688
  norm_num
theorem lane1 : JFv_TX2_InnerMeaning.sum 8 0 1 0 26%2147483647=486849109 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1441901729+1483149559*399835360+655227887*631199233+39062738*960487500+729079828*1991798734+67370206*636832731+1685049618*729538841+385547620*429217738+1786803209*1977199940+779721715*1772669964+594709522*2102866707+338788461*1766067030+526756808*1811189043+184076238*1769320897+1852498770*1149560869+2102463508*1084615208+1086671526*1498576196+1147694576*1130336214+1504805752*1089519845+2005073905*1436775260+185008025*1865493391+1485990146*1046759287+1255280192*335259495+1018329259*1215521203+570157693*1959486198+1511904630*1861395891)%2147483647=486849109
  norm_num
theorem lane2 : JFv_TX2_InnerMeaning.sum 8 0 2 0 26%2147483647=1755038724 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1441901729+1898717401*399835360+1032732628*631199233+1313565596*960487500+1074182998*1991798734+1410213748*636832731+1182702806*729538841+321711020*429217738+2062791928*1977199940+1188803754*1772669964+2038502201*2102866707+735931834*1766067030+1330533011*1811189043+1052874750*1769320897+950153811*1149560869+1225424092*1084615208+1659116453*1498576196+1474177753*1130336214+2073609211*1089519845+1602919019*1436775260+1865917845*1865493391+1085624123*1046759287+1837870964*335259495+1550509101*1215521203+1661725734*1959486198+2066655336*1861395891)%2147483647=1755038724
  norm_num
theorem lane3 : JFv_TX2_InnerMeaning.sum 8 0 3 0 26%2147483647=1456807269 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1441901729+1849775942*399835360+656039795*631199233+1840648083*960487500+246996287*1991798734+1369248953*636832731+1132591724*729538841+92744917*429217738+1719480363*1977199940+1266677922*1772669964+377386917*2102866707+735227219*1766067030+465096431*1811189043+451889791*1769320897+1379836302*1149560869+618598847*1084615208+1624084534*1498576196+1511477847*1130336214+1840812326*1089519845+185546252*1436775260+2145463598*1865493391+82870699*1046759287+1625323762*335259495+1843639311*1215521203+1777269271*1959486198+1645120956*1861395891)%2147483647=1456807269
  norm_num
theorem lane4 : JFv_TX2_InnerMeaning.sum 8 0 4 0 26%2147483647=748974773 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1441901729+1112406525*399835360+1345999435*631199233+752376469*960487500+634588140*1991798734+1419170319*636832731+1702860885*729538841+710076517*429217738+1256487405*1977199940+1114745059*1772669964+1137838899*2102866707+1254184109*1766067030+1038210451*1811189043+274378589*1769320897+171986381*1149560869+1536678585*1084615208+1305878831*1498576196+1335902916*1130336214+1755193245*1089519845+2023391453*1436775260+293456010*1865493391+1751078325*1046759287+1423042536*335259495+1749638204*1215521203+1345811362*1959486198+1284924881*1861395891)%2147483647=748974773
  norm_num
theorem lane5 : JFv_TX2_InnerMeaning.sum 8 0 5 0 26%2147483647=1782476420 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1441901729+1796814865*399835360+1253123171*631199233+1317611639*960487500+1559245386*1991798734+1866942376*636832731+1973593402*729538841+47019780*429217738+1353487525*1977199940+1840161555*1772669964+2003659556*2102866707+200559114*1766067030+334988447*1811189043+2023650872*1769320897+1296497964*1149560869+34285357*1084615208+1685894190*1498576196+995962325*1130336214+1295624230*1089519845+1199631211*1436775260+1948677857*1865493391+1425322328*1046759287+1466877680*335259495+702011012*1215521203+937706871*1959486198+455802666*1861395891)%2147483647=1782476420
  norm_num
theorem lane6 : JFv_TX2_InnerMeaning.sum 8 0 6 0 26%2147483647=2066500345 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1441901729+1838939499*399835360+1353876630*631199233+1258713036*960487500+1947503436*1991798734+1271796599*636832731+1660157177*729538841+564707688*429217738+1858113864*1977199940+1015817431*1772669964+1264608004*2102866707+735383960*1766067030+221696734*1811189043+1297524163*1769320897+109088572*1149560869+792206628*1084615208+1921581249*1498576196+94118806*1130336214+476103426*1089519845+239612482*1436775260+177052717*1865493391+826458039*1046759287+1923715623*335259495+1014161165*1215521203+1341609618*1959486198+786325583*1861395891)%2147483647=2066500345
  norm_num
theorem lane7 : JFv_TX2_InnerMeaning.sum 8 0 7 0 26%2147483647=1737870698 := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change (0+0*1441901729+418714188*399835360+1675147475*631199233+1674326661*960487500+547797802*1991798734+2073962627*636832731+897270857*729538841+1582958967*429217738+49892701*1977199940+1256824732*1772669964+1435903714*2102866707+742583315*1766067030+1789294768*1811189043+13407412*1769320897+518661610*1149560869+1259751297*1084615208+1695663205*1498576196+2068940067*1130336214+940478841*1089519845+1982757556*1436775260+1956713516*1865493391+863066484*1046759287+522298462*335259495+1343575777*1215521203+771712139*1959486198+157728743*1861395891)%2147483647=1737870698
  norm_num
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 8 0
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
end AspisR1.JFz_TX2_Q8_Head0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw00
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 0#u64 0#u64 0#u64 0#u64⟩,⟨pack 0#u64 0#u64 0#u64 0#u64⟩,0#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2821323740#u64 4228475689#u64 6306317185#u64 3784717945#u64⟩,⟨pack 3072001809#u64 1616563249#u64 2976770736#u64 4148314034#u64⟩,1#usize⟩
def raw0 : Array U64 4#usize := pack 2012872648908581336#u64 4652368498325477930#u64 9042861527788772918#u64 4564116087597709229#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 181916699#u32 2053539874#u32 680012092#u32 778645686#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 2136659036#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1454808535#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 901973532#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 2136659036#u32) (JFs_TX2_RawMath.extend 1454808535#u32) (JFs_TX2_RawMath.extend 901973532#u32) (JFs_TX2_RawMath.extend 323718155#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 323718155#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 181916699#u32) (JFs_TX2_RawMath.extend 2053539874#u32) (JFs_TX2_RawMath.extend 680012092#u32) (JFs_TX2_RawMath.extend 778645686#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 181916699#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 181916699#u32) (JFs_TX2_RawMath.extend 2053539874#u32) (JFs_TX2_RawMath.extend 680012092#u32) (JFs_TX2_RawMath.extend 778645686#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2053539874#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 181916699#u32) (JFs_TX2_RawMath.extend 2053539874#u32) (JFs_TX2_RawMath.extend 680012092#u32) (JFs_TX2_RawMath.extend 778645686#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 680012092#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 181916699#u32) (JFs_TX2_RawMath.extend 2053539874#u32) (JFs_TX2_RawMath.extend 680012092#u32) (JFs_TX2_RawMath.extend 778645686#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 778645686#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 2137577801929629619#u64 1144740074027806241#u64 4647521817608538560#u64 5789557275124365405#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 181916699#u32 2053539874#u32 680012092#u32 778645686#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 447208057#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1244418415#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2052833682#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 447208057#u32) (JFs_TX2_RawMath.extend 1244418415#u32) (JFs_TX2_RawMath.extend 2052833682#u32) (JFs_TX2_RawMath.extend 2086368445#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 2086368445#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 181916699#u32) (JFs_TX2_RawMath.extend 2053539874#u32) (JFs_TX2_RawMath.extend 680012092#u32) (JFs_TX2_RawMath.extend 778645686#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 181916699#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 181916699#u32) (JFs_TX2_RawMath.extend 2053539874#u32) (JFs_TX2_RawMath.extend 680012092#u32) (JFs_TX2_RawMath.extend 778645686#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 2053539874#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 181916699#u32) (JFs_TX2_RawMath.extend 2053539874#u32) (JFs_TX2_RawMath.extend 680012092#u32) (JFs_TX2_RawMath.extend 778645686#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 680012092#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 181916699#u32) (JFs_TX2_RawMath.extend 2053539874#u32) (JFs_TX2_RawMath.extend 680012092#u32) (JFs_TX2_RawMath.extend 778645686#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 778645686#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P28.value
    JFr_TX2_Tails18.value0_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value0_0=
      ok (.Ok (pack 181916699#u32 2053539874#u32 680012092#u32 778645686#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (181916699<2147483647 ∧ 2053539874<2147483647) ∧ (680012092<2147483647 ∧ 778645686<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P28.value=
      ok (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      0#usize=ok (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32,pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32])
      1#usize=ok (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 2136659036#u32 1454808535#u32 901973532#u32 323718155#u32) (pack 181916699#u32 2053539874#u32 680012092#u32 778645686#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 0#u64 0#u64 0#u64 0#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 447208057#u32 1244418415#u32 2052833682#u32 2086368445#u32) (pack 181916699#u32 2053539874#u32 680012092#u32 778645686#u32)=ok after.c1 := by
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
end AspisR1.JFz_TX2_Q8_Raw00
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw01
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 2821323740#u64 4228475689#u64 6306317185#u64 3784717945#u64⟩,⟨pack 3072001809#u64 1616563249#u64 2976770736#u64 4148314034#u64⟩,1#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6051686655#u64 6159800077#u64 12338149606#u64 7746012225#u64⟩,⟨pack 7493879466#u64 3751888260#u64 8273672563#u64 4954066442#u64⟩,2#usize⟩
def raw0 : Array U64 4#usize := pack 6042930629821190747#u64 2322372393565698334#u64 9021312484746866069#u64 4308336313524288431#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 949874204#u32 1035877054#u32 8813177#u32 789629886#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1906135911#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 366206321#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 1502152916#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1906135911#u32) (JFs_TX2_RawMath.extend 366206321#u32) (JFs_TX2_RawMath.extend 1502152916#u32) (JFs_TX2_RawMath.extend 1309564201#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1309564201#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 949874204#u32) (JFs_TX2_RawMath.extend 1035877054#u32) (JFs_TX2_RawMath.extend 8813177#u32) (JFs_TX2_RawMath.extend 789629886#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 949874204#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 949874204#u32) (JFs_TX2_RawMath.extend 1035877054#u32) (JFs_TX2_RawMath.extend 8813177#u32) (JFs_TX2_RawMath.extend 789629886#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1035877054#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 949874204#u32) (JFs_TX2_RawMath.extend 1035877054#u32) (JFs_TX2_RawMath.extend 8813177#u32) (JFs_TX2_RawMath.extend 789629886#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 8813177#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 949874204#u32) (JFs_TX2_RawMath.extend 1035877054#u32) (JFs_TX2_RawMath.extend 8813177#u32) (JFs_TX2_RawMath.extend 789629886#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 789629886#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 4975832926495511612#u64 895601979737954001#u64 8885373962395708846#u64 1529701021877641317#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 949874204#u32 1035877054#u32 8813177#u32 789629886#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 644775892#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 239709031#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 459845291#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 644775892#u32) (JFs_TX2_RawMath.extend 239709031#u32) (JFs_TX2_RawMath.extend 459845291#u32) (JFs_TX2_RawMath.extend 570718651#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 570718651#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 949874204#u32) (JFs_TX2_RawMath.extend 1035877054#u32) (JFs_TX2_RawMath.extend 8813177#u32) (JFs_TX2_RawMath.extend 789629886#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 949874204#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 949874204#u32) (JFs_TX2_RawMath.extend 1035877054#u32) (JFs_TX2_RawMath.extend 8813177#u32) (JFs_TX2_RawMath.extend 789629886#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1035877054#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 949874204#u32) (JFs_TX2_RawMath.extend 1035877054#u32) (JFs_TX2_RawMath.extend 8813177#u32) (JFs_TX2_RawMath.extend 789629886#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 8813177#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 949874204#u32) (JFs_TX2_RawMath.extend 1035877054#u32) (JFs_TX2_RawMath.extend 8813177#u32) (JFs_TX2_RawMath.extend 789629886#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 789629886#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P26.value
    JFr_TX2_Tails18.value1_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value1_0=
      ok (.Ok (pack 949874204#u32 1035877054#u32 8813177#u32 789629886#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (949874204<2147483647 ∧ 1035877054<2147483647) ∧ (8813177<2147483647 ∧ 789629886<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P26.value=
      ok (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      0#usize=ok (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32,pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32])
      1#usize=ok (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 1906135911#u32 366206321#u32 1502152916#u32 1309564201#u32) (pack 949874204#u32 1035877054#u32 8813177#u32 789629886#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 2821323740#u64 4228475689#u64 6306317185#u64 3784717945#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 644775892#u32 239709031#u32 459845291#u32 570718651#u32) (pack 949874204#u32 1035877054#u32 8813177#u32 789629886#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 3072001809#u64 1616563249#u64 2976770736#u64 4148314034#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q8_Raw01
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Raw02
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def before : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 6051686655#u64 6159800077#u64 12338149606#u64 7746012225#u64⟩,⟨pack 7493879466#u64 3751888260#u64 8273672563#u64 4954066442#u64⟩,2#usize⟩
def after : FIo_Native.fast_pairing.EbyKDot := ⟨⟨pack 9221035900#u64 6998818447#u64 18156018491#u64 10722687819#u64⟩,⟨pack 10717581113#u64 5658170803#u64 14892517225#u64 8449018265#u64⟩,3#usize⟩
def raw0 : Array U64 4#usize := pack 5088709643596396946#u64 1128409054967796581#u64 9980084980682120578#u64 2179868482909999455#u64
theorem pair0 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1524118751#u32 532675932#u32 483065892#u32 631876546#u32)=ok raw0 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 509504871#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 562297437#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 830444110#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 509504871#u32) (JFs_TX2_RawMath.extend 562297437#u32) (JFs_TX2_RawMath.extend 830444110#u32) (JFs_TX2_RawMath.extend 750558315#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 750558315#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1524118751#u32) (JFs_TX2_RawMath.extend 532675932#u32) (JFs_TX2_RawMath.extend 483065892#u32) (JFs_TX2_RawMath.extend 631876546#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1524118751#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1524118751#u32) (JFs_TX2_RawMath.extend 532675932#u32) (JFs_TX2_RawMath.extend 483065892#u32) (JFs_TX2_RawMath.extend 631876546#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 532675932#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1524118751#u32) (JFs_TX2_RawMath.extend 532675932#u32) (JFs_TX2_RawMath.extend 483065892#u32) (JFs_TX2_RawMath.extend 631876546#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 483065892#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1524118751#u32) (JFs_TX2_RawMath.extend 532675932#u32) (JFs_TX2_RawMath.extend 483065892#u32) (JFs_TX2_RawMath.extend 631876546#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 631876546#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
def raw1 : Array U64 4#usize := pack 6332642320724371272#u64 3762021921985972780#u64 11180411465506092027#u64 5935407962126491487#u64
theorem pair1 : FIo_Native.fast_pairing.canonical.Q.raw
    (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1524118751#u32 532675932#u32 483065892#u32 631876546#u32)=ok raw1 := by
  have r0 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1775007834#u32) := rfl
  have r1 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 1847964904#u32) := rfl
  have r2 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 2126955715#u32) := rfl
  have r3 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1775007834#u32) (JFs_TX2_RawMath.extend 1847964904#u32) (JFs_TX2_RawMath.extend 2126955715#u32) (JFs_TX2_RawMath.extend 1829355625#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 1829355625#u32) := rfl
  have r4 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1524118751#u32) (JFs_TX2_RawMath.extend 532675932#u32) (JFs_TX2_RawMath.extend 483065892#u32) (JFs_TX2_RawMath.extend 631876546#u32)) 0#usize=ok (JFs_TX2_RawMath.extend 1524118751#u32) := rfl
  have r5 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1524118751#u32) (JFs_TX2_RawMath.extend 532675932#u32) (JFs_TX2_RawMath.extend 483065892#u32) (JFs_TX2_RawMath.extend 631876546#u32)) 1#usize=ok (JFs_TX2_RawMath.extend 532675932#u32) := rfl
  have r6 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1524118751#u32) (JFs_TX2_RawMath.extend 532675932#u32) (JFs_TX2_RawMath.extend 483065892#u32) (JFs_TX2_RawMath.extend 631876546#u32)) 2#usize=ok (JFs_TX2_RawMath.extend 483065892#u32) := rfl
  have r7 : Array.index_usize (pack (JFs_TX2_RawMath.extend 1524118751#u32) (JFs_TX2_RawMath.extend 532675932#u32) (JFs_TX2_RawMath.extend 483065892#u32) (JFs_TX2_RawMath.extend 631876546#u32)) 3#usize=ok (JFs_TX2_RawMath.extend 631876546#u32) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,
    r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,
    JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,JFs_TX2_RawMath.twice_pp,
    JFs_TX2_RawMath.triple_p,lift]
  rfl
theorem source : FIo_Native.fast_pairing.EbyKDot.push before JFw_TX2_P27.value
    JFr_TX2_Tails18.value2_0=ok (.Ok (),after) := by
  have full : ¬before.count≥FIo_Native.fast_pairing.MAX_TERMS := by
    unfold before FIo_Native.fast_pairing.MAX_TERMS
    decide
  have checked : FIo_Native.fast_pairing.checked_q JFr_TX2_Tails18.value2_0=
      ok (.Ok (pack 1524118751#u32 532675932#u32 483065892#u32 631876546#u32)) := by
    apply JFs_TX2_CheckedQ.source
    change (1524118751<2147483647 ∧ 532675932<2147483647) ∧ (483065892<2147483647 ∧ 631876546<2147483647)
    omega
  have hw : FIo_Native.fast_pairing.canonical.Q.from_wide JFw_TX2_P27.value=
      ok (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32]) := rfl
  have r0 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      0#usize=ok (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) := rfl
  have r1 : Array.index_usize (Array.make 2#usize [pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32,pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32])
      1#usize=ok (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) := rfl
  have d0 : FIo_Native.fast_pairing.canonical.Dot.push before.c0
      (pack 509504871#u32 562297437#u32 830444110#u32 750558315#u32) (pack 1524118751#u32 532675932#u32 483065892#u32 631876546#u32)=ok after.c0 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair0,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 6051686655#u64 6159800077#u64 12338149606#u64 7746012225#u64⟩ raw0=_
    simp only [raw0,JFw_TX2_FoldPush.source]
    rfl
  have d1 : FIo_Native.fast_pairing.canonical.Dot.push before.c1
      (pack 1775007834#u32 1847964904#u32 2126955715#u32 1829355625#u32) (pack 1524118751#u32 532675932#u32 483065892#u32 631876546#u32)=ok after.c1 := by
    simp only [FIo_Native.fast_pairing.canonical.Dot.push,pair1,bind_tc_ok]
    change JFw_TX2_FoldPush.loopCall {start:=0#usize,«end»:=4#usize}
      ⟨pack 7493879466#u64 3751888260#u64 8273672563#u64 4954066442#u64⟩ raw1=_
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
end AspisR1.JFz_TX2_Q8_Raw02
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Tail0
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
def value : FIo_Install.NE := ⟨⟨⟨631101312#u32,556367506#u32⟩,⟨976149315#u32,2132753231#u32⟩⟩,⟨⟨2127646525#u32,1363203509#u32⟩,⟨2007615343#u32,2006567324#u32⟩⟩⟩
theorem finish : FIo_Native.fast_pairing.EbyKDot.finish JFz_TX2_Q8_Raw02.after=ok value := by
  obtain ⟨out,a,b,run,_,h,va,vb⟩ := JFv_TX2_EbyKFinishMeaning.source JFz_TX2_Q8_Raw02.after
  obtain ⟨a0,a1,a2,a3,ea⟩ := shape a
  obtain ⟨a4,a5,a6,a7,eb⟩ := shape b
  rw [ea] at va
  rw [eb] at vb
  have h0 := va 0
  change a0.val=9221035900%2147483647 at h0
  norm_num at h0
  have e0 : a0=631101312#u32 := UScalar.eq_of_val_eq h0
  have h1 := va 1
  change a1.val=6998818447%2147483647 at h1
  norm_num at h1
  have e1 : a1=556367506#u32 := UScalar.eq_of_val_eq h1
  have h2 := va 2
  change a2.val=18156018491%2147483647 at h2
  norm_num at h2
  have e2 : a2=976149315#u32 := UScalar.eq_of_val_eq h2
  have h3 := va 3
  change a3.val=10722687819%2147483647 at h3
  norm_num at h3
  have e3 : a3=2132753231#u32 := UScalar.eq_of_val_eq h3
  have h4 := vb 0
  change a4.val=10717581113%2147483647 at h4
  norm_num at h4
  have e4 : a4=2127646525#u32 := UScalar.eq_of_val_eq h4
  have h5 := vb 1
  change a5.val=5658170803%2147483647 at h5
  norm_num at h5
  have e5 : a5=1363203509#u32 := UScalar.eq_of_val_eq h5
  have h6 := vb 2
  change a6.val=14892517225%2147483647 at h6
  norm_num at h6
  have e6 : a6=2007615343#u32 := UScalar.eq_of_val_eq h6
  have h7 := vb 3
  change a7.val=8449018265%2147483647 at h7
  norm_num at h7
  have e7 : a7=2006567324#u32 := UScalar.eq_of_val_eq h7
  rw [ea,eb,e0,e1,e2,e3,e4,e5,e6,e7] at h
  have limbs : JFv_TX2_FromLimbsMeaning.limbs out=JFv_TX2_FromLimbsMeaning.limbs value := Subtype.ext h
  have same : out=value := JFw_TX2_CellUnique.source out value (by intro j;rw [limbs])
  exact same ▸ run
theorem source : JFs_TX2_DotSuffix.tail
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  have g28 := JFw_TX2_PowerReads.source 28
  have g26 := JFw_TX2_PowerReads.source 26
  have g27 := JFw_TX2_PowerReads.source 27
  change Array.index_usize JFr_TX2_FirstLane.native 28#usize=ok JFw_TX2_P28.value at g28
  change Array.index_usize JFr_TX2_FirstLane.native 26#usize=ok JFw_TX2_P26.value at g26
  change Array.index_usize JFr_TX2_FirstLane.native 27#usize=ok JFw_TX2_P27.value at g27
  erw [JFs_TX2_TailStages.body _ _ (0:Fin 4)]
  simp only [JFs_TX2_TailStages.source,bind_tc_ok,g28,g26,g27,
    show FIo_Native.fast_pairing.EbyKDot.new=ok JFz_TX2_Q8_Raw00.before from rfl,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 0 0) (JFr_TX2_Tails.stop 0 0)=ok JFr_TX2_Tails18.value0_0
      from JFr_TX2_Tails18.source0_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 0 1) (JFr_TX2_Tails.stop 0 1)=ok JFr_TX2_Tails18.value1_0
      from JFr_TX2_Tails18.source1_0,
    show JFr_TX2_TailRead.read (JFr_TX2_Windows.array (JFn_Values.position 8))
      (JFr_TX2_Tails.offset 0 2) (JFr_TX2_Tails.stop 0 2)=ok JFr_TX2_Tails18.value2_0
      from JFr_TX2_Tails18.source2_0,
    JFz_TX2_Q8_Raw00.source,Aeneas.Std.uncurry,core.result.Result.unwrap]
  have same1 : JFz_TX2_Q8_Raw00.after=JFz_TX2_Q8_Raw01.before := rfl
  have same2 : JFz_TX2_Q8_Raw01.after=JFz_TX2_Q8_Raw02.before := rfl
  simp only [same1,JFz_TX2_Q8_Raw01.source,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.unwrap,same2,JFz_TX2_Q8_Raw02.source,finish]
#print axioms finish
#print axioms source
end AspisR1.JFz_TX2_Q8_Tail0
end

set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q8_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨988443000#u32,1043216615#u32⟩,⟨583704392#u32,1442076853#u32⟩⟩,⟨⟨729137651#u32,998196282#u32⟩,⟨1926632041#u32,1596954375#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((988443000<2147483647 ∧ 1043216615<2147483647) ∧ (583704392<2147483647 ∧ 1442076853<2147483647)) ∧
    ((729137651<2147483647 ∧ 998196282<2147483647) ∧ (1926632041<2147483647 ∧ 1596954375<2147483647))
  omega
theorem addition : decode JFz_TX2_Q8_Head0.value+decode JFz_TX2_Q8_Tail0.value=decode value := by
  change (⟨⟨⟨357341688,486849109⟩,⟨1755038724,1456807269⟩⟩,⟨⟨748974773,1782476420⟩,⟨2066500345,1737870698⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨631101312,556367506⟩,⟨976149315,2132753231⟩⟩,⟨⟨2127646525,1363203509⟩,⟨2007615343,2006567324⟩⟩⟩=⟨⟨⟨988443000,1043216615⟩,⟨583704392,1442076853⟩⟩,⟨⟨729137651,998196282⟩,⟨1926632041,1596954375⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 8)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 8 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q8_Head0.value JFz_TX2_Q8_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q8_Head0.source,
      JFz_TX2_Q8_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q8_Head0.value := by
    change ((357341688<2147483647 ∧ 486849109<2147483647) ∧ (1755038724<2147483647 ∧ 1456807269<2147483647)) ∧
      ((748974773<2147483647 ∧ 1782476420<2147483647) ∧ (2066500345<2147483647 ∧ 1737870698<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q8_Tail0.value := by
    change ((631101312<2147483647 ∧ 556367506<2147483647) ∧ (976149315<2147483647 ∧ 2132753231<2147483647)) ∧
      ((2127646525<2147483647 ∧ 1363203509<2147483647) ∧ (2007615343<2147483647 ∧ 2006567324<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q8_Dot0
end
